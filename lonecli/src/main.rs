mod solver;
mod solvitaire;
mod tracking;
mod tui;

use bpci::{Interval, NSuccessesSample, WilsonScore};
use clap::{Args, Parser, Subcommand, ValueEnum};
use lonelybot::convert::convert_moves;
use lonelybot::engine::SolitaireEngine;
use lonelybot::mcts_solver::pick_moves;
use lonelybot::pruning::{CyclePruner, FullPruner, NoPruner};
use lonelybot::shuffler::{self, CardDeck, U256};
use lonelybot::state::{Encode, Solitaire};
use lonelybot::tracking::DefaultTerminateSignal;
use lonelybot::traverse::Control;
use rand::prelude::*;
use solvitaire::Solvitaire;
use std::collections::HashSet;
use std::fs::File;
use std::num::NonZeroU8;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;
use std::{io::Write, time::Instant};
use std::{thread, time};

use lonelybot::solver::SearchResult;
use lonelybot::standard::{Pos, StandardHistoryVec, StandardSolitaire};

use crate::tui::print_game;

#[derive(ValueEnum, Clone, Copy)]
enum SeedType {
    /// Doc comment
    Default,
    Solvitaire,
    KlondikeSolver,
    Greenfelt,
    Exact,
    Microsoft,
}

#[derive(Args, Clone)]
struct StringSeed {
    seed_type: SeedType,
    seed: String,
}

struct Seed {
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
                SeedType::Default => "L",
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
    pub(crate) const fn seed(&self) -> U256 {
        self.seed
    }

    #[must_use]
    pub(crate) fn increase(&self, step: u32) -> Self {
        Self {
            seed_type: self.seed_type,
            seed: self.seed() + step,
        }
    }
}

#[must_use]
fn shuffle(s: &Seed) -> CardDeck {
    let seed = s.seed;
    match s.seed_type {
        SeedType::Default => shuffler::default_shuffle(seed.as_u64()),
        SeedType::Solvitaire => shuffler::solvitaire_shuffle(seed.as_u32()),
        SeedType::KlondikeSolver => shuffler::ks_shuffle(seed.as_u32()),
        SeedType::Greenfelt => shuffler::greenfelt_shuffle(seed.as_u32()),
        SeedType::Exact => shuffler::exact_shuffle(seed).unwrap(),
        SeedType::Microsoft => shuffler::microsoft_shuffle(seed).unwrap(),
    }
}

fn benchmark(seed: &Seed, draw_step: NonZeroU8) {
    let mut rng = SmallRng::seed_from_u64(seed.seed().as_u64());

    let mut total_moves = 0u32;
    let now = Instant::now();
    for i in 0..100 {
        let mut game: SolitaireEngine<FullPruner> =
            Solitaire::new(&shuffle(&seed.increase(i)), draw_step).into();
        for _ in 0..100 {
            let moves = game.list_moves_dom();

            if moves.is_empty() {
                break;
            }
            assert!(game.do_move(*moves.choose(&mut rng).unwrap()));
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

fn do_random(seed: &Seed, draw_step: NonZeroU8) {
    const TOTAL_GAME: u32 = 10000;

    let mut total_win = 0;
    for i in 0..TOTAL_GAME {
        let mut game: SolitaireEngine<CyclePruner> =
            Solitaire::new(&shuffle(&seed.increase(i)), draw_step).into();

        loop {
            if game.state().is_win() {
                total_win += 1;
                break;
            }
            let moves = game.list_moves_dom();

            if moves.is_empty() {
                break;
            }

            let m = &moves[0];

            game.do_move(*m);
        }
    }
    println!("Total win {total_win}/{TOTAL_GAME}");
}

fn ucb1(n_sucess: usize, n_visit: usize, n_total: usize) -> f64 {
    const C: f64 = 2.;

    #[allow(clippy::cast_precision_loss)]
    if n_visit == 0 {
        f64::INFINITY
    } else {
        n_sucess as f64 / n_visit as f64 + C * ((n_total as f64).ln() / n_visit as f64).sqrt()
    }
}

fn do_hop(seed: &Seed, draw_step: NonZeroU8, verbose: bool) -> bool {
    const N_TIMES: usize = 3000;
    const LIMIT: usize = 1000;

    let mut game: SolitaireEngine<NoPruner> = Solitaire::new(&shuffle(seed), draw_step).into();
    let mut rng = SmallRng::seed_from_u64(seed.seed().as_u64());

    while !game.state().is_win() {
        let mut gg = game.state().clone();
        gg.hidden_clear();
        let best = pick_moves(
            &mut gg,
            &mut rng,
            N_TIMES,
            LIMIT,
            &DefaultTerminateSignal {},
            ucb1,
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
            game.do_move(m);
        }
    }
    if verbose {
        println!("Solved");
    }
    true
}

fn map_pos(p: Pos) -> char {
    match p {
        Pos::Deck => 'A',
        Pos::Stack(id) => char::from_u32('B' as u32 + u32::from(id)).unwrap(),
        Pos::Pile(id) => char::from_u32('F' as u32 + u32::from(id)).unwrap(),
    }
}

fn print_moves_minimal_klondike(moves: &StandardHistoryVec) {
    for m in moves {
        match (m.from, m.to) {
            (Pos::Deck, Pos::Deck) => print!("@"),
            (from, to) => print!("{}{} ", map_pos(from), map_pos(to)),
        }
    }
}

fn test_solve(seed: &Seed, draw_step: NonZeroU8, terminated: &Arc<AtomicBool>) {
    let shuffled_deck = shuffle(seed);

    let g: Solitaire = Solitaire::new(&shuffled_deck, draw_step);
    let mut g_standard = StandardSolitaire::from(&g);

    let now = Instant::now();
    let res = solver::run_solve(g, true, terminated);
    println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    println!("Statistic\n{}", res.1);
    match res.0 {
        SearchResult::Solved => {
            let m = res.2.unwrap();
            println!("Solvable in {} moves", m.len());
            println!();
            let moves = convert_moves(&mut g_standard, &m[..]).unwrap();
            for x in m {
                print!("{x}, ");
            }
            println!();
            println!();
            for m in &moves {
                print!("{m}  ");
            }
            println!();
            println!();
            print_moves_minimal_klondike(&moves);
            println!();
        }
        SearchResult::Unsolvable => println!("Impossible"),
        SearchResult::Terminated => println!("Terminated"),
        SearchResult::Crashed => println!("Crashed"),
    }
}

fn rand_solve(seed: &Seed, draw_step: NonZeroU8, start_seed: u64, terminated: &Arc<AtomicBool>) {
    let shuffled_deck = shuffle(seed);

    let g: Solitaire = Solitaire::new(&shuffled_deck, draw_step);

    let mut game: SolitaireEngine<CyclePruner> = g.into();
    let mut rng = SmallRng::seed_from_u64(start_seed);

    loop {
        if rng.random_bool(0.1) || game.state().is_win() {
            break;
        }
        let moves = game.list_moves_dom();

        let Some(m) = moves.choose(&mut rng) else {
            break;
        };

        game.do_move(*m);
    }

    println!("{}", Solvitaire(game.state().into()));

    let now = Instant::now();
    let res = solver::run_solve(game.into_state(), true, terminated);
    println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    println!("Statistic\n{}", res.1);
    match res.0 {
        SearchResult::Solved => {
            let m = res.2.unwrap();
            println!("Solvable in {} moves", m.len());
            for x in m {
                print!("{x}, ");
            }
        }
        SearchResult::Unsolvable => println!("Impossible"),
        SearchResult::Terminated => println!("Terminated"),
        SearchResult::Crashed => println!("Crashed"),
    }
}

fn test_graph(seed: &Seed, draw_step: NonZeroU8, path: &String, terminated: &Arc<AtomicBool>) {
    let shuffled_deck = shuffle(seed);

    let g: Solitaire = Solitaire::new(&shuffled_deck, draw_step);

    let now = Instant::now();
    let res = solver::run_graph(g, true, terminated);
    println!("Run in {} ms", now.elapsed().as_secs_f64() * 1000f64);
    println!("Statistic\n{}", res.1);
    match res.0 {
        Some((res, graph)) => {
            println!("Graphed in {} edges", graph.len());
            if res == Control::Ok {
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

fn game_loop(seed: &Seed, draw_step: NonZeroU8) {
    let shuffled_deck = shuffle(seed);

    let mut game: SolitaireEngine<FullPruner> = Solitaire::new(&shuffled_deck, draw_step).into();

    let mut line: String = String::new();

    let mut game_state = HashSet::<Encode>::new();

    loop {
        print_game(game.state());
        if !game_state.insert(game.encode()) {
            println!("Already existed state");
        }

        let moves = game.list_moves_dom();

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
                assert!(game.do_move(moves[id]));
            } else {
                game.undo_move();
                println!("Undo!!");
            }
        } else {
            println!("Invalid move");
        }
    }
}

fn solve_loop(org_seed: &Seed, draw_step: NonZeroU8, terminated: &Arc<AtomicBool>) {
    let mut cnt_terminated = 0u32;
    let mut cnt_solve = 0u32;
    let mut cnt_total = 0u32;

    let start = Instant::now();

    for step in 0.. {
        let seed = org_seed.increase(step);
        let shuffled_deck = shuffle(&seed);
        let g = Solitaire::new(&shuffled_deck, draw_step);

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
        draw_step: NonZeroU8,
    },

    Solve {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
    },

    RandSolve {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
        start_seed: u64,
    },

    Graph {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
        out: String,
    },

    Play {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
    },

    Random {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
    },

    Rate {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
    },

    Hop {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
    },
    HopLoop {
        #[command(flatten)]
        seed: StringSeed,
        draw_step: NonZeroU8,
    },
}

fn main() {
    let args = Cli::parse().command;

    match &args {
        Commands::Print { seed } => {
            let shuffled_deck = shuffle(&seed.into());
            let g = StandardSolitaire::new(&shuffled_deck, NonZeroU8::MIN);

            println!("{}", Solvitaire(g));
        }
        Commands::Solve { seed, draw_step } => {
            test_solve(&seed.into(), *draw_step, &handling_signal());
        }
        Commands::RandSolve {
            seed,
            draw_step,
            start_seed,
        } => {
            rand_solve(&seed.into(), *draw_step, *start_seed, &handling_signal());
        }
        Commands::Graph {
            seed,
            draw_step,
            out,
        } => test_graph(&seed.into(), *draw_step, out, &handling_signal()),
        Commands::Play { seed, draw_step } => game_loop(&seed.into(), *draw_step),
        Commands::Bench { seed, draw_step } => benchmark(&seed.into(), *draw_step),
        Commands::Rate { seed, draw_step } => {
            solve_loop(&seed.into(), *draw_step, &handling_signal());
        }
        Commands::Exact { seed } => {
            let shuffled_deck = shuffle(&seed.into());
            println!("{}", shuffler::encode_shuffle(shuffled_deck).unwrap());
        }
        Commands::Random { seed, draw_step } => do_random(&seed.into(), *draw_step),
        Commands::Hop { seed, draw_step } => {
            do_hop(&seed.into(), *draw_step, true);
        }
        Commands::HopLoop { seed, draw_step } => {
            let mut cnt_solve: u32 = 0;
            for i in 0.. {
                let s: Seed = seed.into();
                let start = time::Instant::now();

                cnt_solve += u32::from(do_hop(&s.increase(i), *draw_step, false));
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
