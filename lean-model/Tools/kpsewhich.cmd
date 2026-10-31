@echo off
rem Minimal kpsewhich stand-in for plasTeX on a TeX-less Windows machine.
rem plasTeX shells out to kpsewhich to locate files; when the tool is
rem missing the subprocess returns empty (no exception), so the
rem TEXINPUTS fallback never runs and every lookup hard-fails.
rem This shim resolves the given file relative to the current
rem directory, or anywhere on PATH; prints nothing when not found.
if exist "%~1" (
  echo %~f1
  exit /b 0
)
for %%I in ("%~1") do if not "%%~$PATH:I"=="" echo %%~$PATH:I
exit /b 0
