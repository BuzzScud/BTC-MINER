$ErrorActionPreference = 'Stop'
$env:PYTHONUTF8 = '1'
Set-Location $PSScriptRoot
if (Get-Command py -ErrorAction SilentlyContinue) {
    & py -3 scripts/setup_terminal.py @args
} elseif (Get-Command python -ErrorAction SilentlyContinue) {
    & python scripts/setup_terminal.py @args
} else {
    Write-Host 'Python 3.9+ is required. Download: https://www.python.org/downloads/windows/'
    $answer = Read-Host 'Install Python 3.12 using winget? [y/N]'
    if ($answer -match '^(y|yes)$' -and (Get-Command winget -ErrorAction SilentlyContinue)) {
        & winget install --exact --id Python.Python.3.12
        Write-Host 'Open a new terminal and rerun setup.ps1.'
    }
    exit 1
}
exit $LASTEXITCODE
