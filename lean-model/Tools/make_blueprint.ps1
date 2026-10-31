# make_blueprint.ps1 -- build the Orig2 blueprint web pages.
#
# The standard entry point `leanblueprint web` cannot be used here:
# lean-model is a subdirectory of the lonelybot git repo (no .git of
# its own), so the client's Repo(".", search_parent_directories=True)
# finds the outer repo and dies on its missing lakefile.  This script
# runs exactly what `leanblueprint web` runs internally:
#   plastex -c plastex.cfg web.tex   (from blueprint/src)
#
# The Tools\kpsewhich.cmd shim is prepended to PATH because plasTeX
# requires a kpsewhich executable to locate files (see the shim's
# header for why a missing kpsewhich is fatal rather than degrading
# to the TEXINPUTS fallback on Windows).
#
# Output: blueprint/web/  (open dep_graph_document.html for the graph;
# serve it first:  python -m http.server 8123 -d blueprint\web )

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot   # lean-model
$src = Join-Path $root "blueprint\src"

if (-not (Get-Command plastex -ErrorAction SilentlyContinue)) {
    Write-Error "plastex not found -- pip install leanblueprint"
}

$env:PATH = "$PSScriptRoot;$env:PATH"
Push-Location $src
try {
    plastex -c plastex.cfg web.tex
} finally {
    Pop-Location
}

Write-Host ""
Write-Host "Blueprint built at blueprint\web\"
Write-Host "Graph page: blueprint\web\dep_graph_document.html"
Write-Host "To view:    python -m http.server 8123 -d blueprint\web"
Write-Host "            then open http://localhost:8123/dep_graph_document.html"
