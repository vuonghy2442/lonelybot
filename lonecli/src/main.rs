mod solver;
mod tracking;
mod tui;

use bpci::{Interval, NSuccessesSample, WilsonScore};
use clap::{Args, Parser, Subcommand, ValueEnum};
use lonelybot::convert::convert_moves;
use lonelybot::engine::{Encode, Move, MoveVec, Solitaire, UndoInfo};
use lonelybot::formatter::Solvitaire;
use lonelybot::mcts_solver::pick_moves;
use lonelybot::pruning::PruneInfo;
use lonelybot::shuffler::{self, CardDeck, U256};
use lonelybot::tracking::DefaultTerminateSignal;
use lonelybot::traverse::ControlFlow;
use rand::prelude::*;
use std::collections::HashSet;
use std::fs::File;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;
use std::{io::Write, time::Instant};
use std::{thread, time};

use lonelybot::solver::SearchResult;
use lonelybot::standard::{Pos, StandardHistoryVec, StandardSolitaire};

use crate::tui::print_game;

#[derive(ValueEnum, Clone, Copy)]
pub enum SeedType {
    /// Doc comment
    Default,
    Legacy,
    Solvitaire,
    KlondikeSolver,
    Greenfelt,
    Exact,
    Microsoft,
}

#[derive(Args, Clone)]
pub struct StringSeed {
    seed_type: SeedType,
    seed: String,
}

pub struct Seed {
    seed_type: SeedType,
    seed: U256,
}

impl From<&StringSeed> for Seed {
    fn from(value: &StringSeed) -> Self {
        Seed {
            seed_type: value.seed_type,
            seed: U256::from_dec_str(&value.seed).unwrap(),
        }
    }
}

impl std::fmt::Display for Seed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}-{}",
            match self.seed_type {
                SeedType::Default => "D",
                SeedType::Legacy => "L",
                SeedType::Solvitaire => "S",
                SeedType::KlondikeSolver => "K",
                SeedType::Greenfelt => "G",
                SeedType::Exact => "E",
                SeedType::Microsoft => "M",
            },
            self.seed
        )
    }
}

impl Seed {
    #[must_use]
    pub const fn seed(&self) -> U256 {
        self.seed
    }

    #[must_use]
    pub fn increase(&self, step: u32) -> Self {
        Self {
            seed_type: self.seed_type,
            seed: self.seed() + step,
        }
    }
}

#[must_use]
pub fn shuffle(s: &Seed) -> CardDeck {
    let seed = s.seed;
    match s.seed_type {
        SeedType::Default => shuffler::default_shuffle(seed.as_u64()),
        SeedType::Legacy => shuffler::legacy_shuffle(seed.as_u64()),
        SeedType::Solvitaire => shuffler::solvitaire_shuffle(seed.as_u32()),
        SeedType::KlondikeSolver => shuffler::ks_shuffle(seed.as_u32()),
        SeedType::Greenfelt => shuffler::greenfelt_shuffle(seed.as_u32()),
        SeedType::Exact => shuffler::exact_shuffle(seed).unwrap(),
        SeedType::Microsoft => shuffler::microsoft_shuffle(seed).unwrap(),
    }
}

fn benchmark(seed: &Seed) {
    let mut rng = StdRng::seed_from_u64(seed.seed().as_u64());

    let mut total_moves = 0u32;
    let now = Instant::now();
    for i in 0..100 {
        let mut game = Solitaire::new(&shuffle(&seed.increase(i)), 3);
        for _ in 0..100 {
            let moves = game.list_moves::<true>(&Default::default());

            if moves.is_empty() {
                break;
            }
            game.do_move(moves.choose(&mut rng).unwrap());
            std::hint::black_box(game.encode());
            total_moves += 1;
        }
    }
    println!(
        "{} {} op/s",
        total_moves,
        f64::from(total_moves) / now.elapsed().as_secs_f64()
    );
}

fn do_random(seed: &Seed) {
    const TOTAL_GAME: u32 = 10000;

    let mut total_win = 0;
    for i in 0..TOTAL_GAME {
        let mut game = Solitaire::new(&shuffle(&seed.increase(i)), 3);
        let mut rev_move = None;
        loop {
            if game.is_win() {
                total_win += 1;
                break;
            }
            let moves = game.list_moves::<true>(&Default::default());

            let moves: MoveVec = moves
                .iter()
                .filter(|&&c| Some(c) != rev_move)
                .copied()
                .collect();

            if moves.is_empty() {
                break;
            }

            let m = &moves[0];
            rev_move = game.get_rev_move(m);

            game.do_move(m);
        }
    }
    println!("Total win {total_win}/{TOTAL_GAME}");
}

fn do_hop(seed: &Seed, verbose: bool) -> bool {
    const N_TIMES: usize = 3000;
    const LIMIT: usize = 1000;

    let mut game = Solitaire::new(&shuffle(seed), 3);
    let mut rng = StdRng::seed_from_u64(seed.seed().as_u64());

    while !game.is_win() {
        let mut gg = game.clone();
        gg.get_hidden_mut().clear();
        let best = pick_moves(
            &mut gg,
            &mut rng,
            N_TIMES,
            LIMIT,
            &DefaultTerminateSignal {},
        );
        let Some(best) = best else {
            if verbose {
                println!("Lost");
            }
            return false;
        };
        if verbose {
            for m in &best {
                print!("{m}, ");
            }
            println!();
        }
        for m in best {
            game.do_move(&m);
        }
    }
    if verbose {
        println!("Solved");
    }
    true
}

fn map_pos(p: &Pos) -> char {
    match *p {
        Pos::Deck => 'A',
        Pos::Stack(id) => char::from_u32('B' as u32 + id as u32).unwrap(),
        Pos::Pile(id) => char::from_u32('F' as u32 + id as u32).unwrap(),
    }
}

fn print_moves_minimal_klondike(moves: &StandardHistoryVec) {
    for m in moves {
        if matches!(m, (Pos::Deck, Pos::Deck, _)) {
            print!("@");
        } else {
            print!("{}{} ", map_pos(&m.0), map_pos(&m.1));
        }
    }
}

fn test_solve(seed: &Seed, terminated: &Arc<AtomicBool>) {
    let shuffled_deck = shuffle(seed);

    let g: Solitaire = Solitaire::new(&shuffled_deck, 3);
    let mut g_standard = StandardSolitaire::from(&g);

    let now = Instant::now();
    let res = solver::run_solve(g, true, terminated);
    println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    println!("Statistic\n{}", res.1);
    match res.0 {
        SearchResult::Solved => {
            let m = res.2.unwrap();
            println!("Solvable in {} moves", m.len());
            let moves = convert_moves(&mut g_standard, &m[..]).unwrap();
            for x in m {
                print!("{x}, ");
            }
            println!();
            for m in &moves {
                print!("{:?} {:?} {}, ", m.0, m.1, m.2);
            }
            println!();
            print_moves_minimal_klondike(&moves);
            println!();
        }
        SearchResult::Unsolvable => println!("Impossible"),
        SearchResult::Terminated => println!("Terminated"),
        SearchResult::Crashed => println!("Crashed"),
    }
}

fn test_graph(seed: &Seed, path: &String, terminated: &Arc<AtomicBool>) {
    let shuffled_deck = shuffle(seed);

    let g: Solitaire = Solitaire::new(&shuffled_deck, 3);

    let now = Instant::now();
    let res = solver::run_graph(g, true, terminated);
    println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    println!("Statistic\n{}", res.1);
    match res.0 {
        Some((res, graph)) => {
            println!("Graphed in {} edges", graph.len());
            if res == ControlFlow::Ok {
                let mut f = std::io::BufWriter::new(File::create(path).unwrap());
                writeln!(f, "s,t,e,id").unwrap();
                for (id, e) in graph.iter().skip(1).enumerate() {
                    writeln!(f, "{},{},{:?},{}", e.0, e.1, e.2, id).unwrap();
                }
                println!("Save done");
            } else {
                println!("Unfinished");
            }
        }
        _ => println!("Crashed"),
    }
}

fn game_loop(seed: &Seed) {
    let shuffled_deck = shuffle(seed);

    let mut game = Solitaire::new(&shuffled_deck, 3);

    let mut line = String::new();

    let mut move_hist = Vec::<(Move, UndoInfo)>::new();

    let mut game_state = HashSet::<Encode>::new();

    let mut pruner = PruneInfo::default();

    loop {
        print_game(&game);
        if !game_state.insert(game.encode()) {
            println!("Already existed state");
        }

        let moves = game.list_moves::<true>(&pruner.prune_moves(&game));

        for (i, m) in moves.iter().enumerate() {
            print!("{i}.{m}, ");
        }
        println!();

        println!("Hash: {:?}", game.encode());
        print!("Move: ");
        std::io::stdout().flush().unwrap();
        line.clear();
        let b1 = std::io::stdin().read_line(&mut line);
        if b1.is_err() {
            println!("Can't read");
            continue;
        }
        let res: Option<i8> = line.trim().parse::<i8>().ok();
        if let Some(id) = res {
            let id = usize::try_from(id).unwrap_or(usize::MAX);
            if id < moves.len() {
                pruner = PruneInfo::new(&game, &pruner, &moves[id]);
                let info = game.do_move(&moves[id]);
                move_hist.push((moves[id], info));
            } else {
                let (m, info) = &move_hist.pop().unwrap();
                pruner = PruneInfo::default();
                game.undo_move(m, info);
                println!("Undo!!");
            }
        } else {
            println!("Invalid move");
        }
    }
}

fn solve_loop(org_seed: &Seed, terminated: &Arc<AtomicBool>) {
    let mut cnt_terminated = 0u32;
    let mut cnt_solve = 0u32;
    let mut cnt_total = 0u32;

    let start = Instant::now();

    for step in 0.. {
        let seed = org_seed.increase(step);
        let shuffled_deck = shuffle(&seed);
        let g = Solitaire::new(&shuffled_deck, 3);

        let now = Instant::now();
        let (res, stats, _) = solver::run_solve(g, false, terminated);
        match res {
            SearchResult::Solved => cnt_solve += 1,
            SearchResult::Terminated => cnt_terminated += 1,
            _ => {}
        };

        cnt_total += 1;

        let lower = NSuccessesSample::new(cnt_total, cnt_solve)
            .unwrap()
            .wilson_score(1.960)
            .lower(); //95%
        let higher = NSuccessesSample::new(cnt_total, cnt_solve + cnt_terminated)
            .unwrap()
            .wilson_score(1.960)
            .upper(); //95%
        println!(
            "Run {} {:?}: ({}-{}/{} ~ {:.4}<={:.4}<={:.4}) {} {} {} in {:.2} ms.",
            seed,
            res,
            cnt_solve,
            cnt_terminated,
            cnt_total,
            lower,
            f64::from(cnt_solve) / f64::from(cnt_total),
            higher,
            stats.total_visit(),
            stats.unique_visit(),
            stats.max_depth(),
            now.elapsed().as_secs_f64() * 1000f64,
        );

        if terminated.load(Ordering::Relaxed) {
            thread::sleep(Duration::from_millis(500));
            terminated.store(false, Ordering::Relaxed);
        }
    }

    println!("Total run time: {:?}", start.elapsed());
}

fn handling_signal() -> Arc<AtomicBool> {
    let terminated = Arc::new(AtomicBool::new(false));

    signal_hook::flag::register_conditional_shutdown(
        signal_hook::consts::signal::SIGINT,
        1,
        Arc::clone(&terminated),
    )
    .expect("Can't register hook");

    signal_hook::flag::register(signal_hook::consts::signal::SIGINT, Arc::clone(&terminated))
        .expect("Can't register hook");
    terminated
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Exact {
        #[command(flatten)]
        seed: StringSeed,
    },
    Print {
        #[command(flatten)]
        seed: StringSeed,
    },

    Bench {
        #[command(flatten)]
        seed: StringSeed,
    },

    Solve {
        #[command(flatten)]
        seed: StringSeed,
    },

    Graph {
        #[command(flatten)]
        seed: StringSeed,
        out: String,
    },

    Play {
        #[command(flatten)]
        seed: StringSeed,
    },

    Random {
        #[command(flatten)]
        seed: StringSeed,
    },

    Rate {
        #[command(flatten)]
        seed: StringSeed,
    },

    Hop {
        #[command(flatten)]
        seed: StringSeed,
    },
    HopLoop {
        #[command(flatten)]
        seed: StringSeed,
    },
}

fn main() {
    let args = Cli::parse().command;

    match &args {
        Commands::Print { seed } => {
            let shuffled_deck = shuffle(&seed.into());
            let g = StandardSolitaire::new(&shuffled_deck, 3);

            println!("{}", Solvitaire(g));
        }
        Commands::Solve { seed } => test_solve(&seed.into(), &handling_signal()),
        Commands::Graph { seed, out } => test_graph(&seed.into(), out, &handling_signal()),
        Commands::Play { seed } => game_loop(&seed.into()),
        Commands::Bench { seed } => benchmark(&seed.into()),
        Commands::Rate { seed } => solve_loop(&seed.into(), &handling_signal()),
        Commands::Exact { seed } => {
            let shuffled_deck = shuffle(&seed.into());
            println!("{}", shuffler::encode_shuffle(shuffled_deck).unwrap());
        }
        Commands::Random { seed } => do_random(&seed.into()),
        Commands::Hop { seed } => {
            do_hop(&seed.into(), true);
        }
        Commands::HopLoop { seed } => {
            let mut cnt_solve: u32 = 0;
            for i in 0.. {
                let s: Seed = seed.into();
                let start = time::Instant::now();

                cnt_solve += u32::from(do_hop(&s.increase(i), false));
                let elapsed = start.elapsed();

                let interval = NSuccessesSample::new(i + 1, cnt_solve)
                    .unwrap()
                    .wilson_score(1.960);
                println!(
                    "{}/{} ~ {:.4} < {:.4} < {:.4} in {:?}",
                    cnt_solve,
                    i + 1,
                    interval.lower(),
                    f64::from(cnt_solve) / f64::from(i + 1),
                    interval.upper(),
                    elapsed
                );
            }
        }
    }
}
