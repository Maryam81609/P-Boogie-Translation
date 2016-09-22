@echo off
setlocal
pushd %~dp0
cd ..
goto :start

:help
echo Usage: build [debug|release] [x64|x86] [nosync] [clean|noclean] 
echo nosync - do not update the git submodules.
echo clean - only clean the build
echo noclean - do not clean the build, so do incemental build

goto :exit

:start

set MSBuildPath=
for /F "usebackq tokens=1,2* delims= " %%i in (`reg query HKEY_LOCAL_MACHINE\SOFTWARE\Microsoft\MSBuild\ToolsVersions\14.0 -v MSBuildToolsPath`) do (
   if "%%i" == "MSBuildToolsPath" set MSBuildPath=%%k
)

if not "%MSBuildPath%"=="" goto :step2

echo MSBUILD 14.0 does not appear to be installed.
echo No info found in HKEY_LOCAL_MACHINE\SOFTWARE\Microsoft\MSBuild\ToolsVersions\14.0
goto :eof

:step2
set TAIL=%MSBuildPath:~-6%
if "[%TAIL%]" == "[amd64\]" set MSBuildPath=%MSBuildPath:~0,-6%"
set PATH=%PATH%;%MSBuildPath%
set Configuration=Debug
set Platform=x86
set NoSync=
set CleanOnly=
set NoClean=
set SubmoduleOutOfDate=false

:parseargs
if /I "%1"=="debug" set Configuration=Debug
if /I "%1"=="release" set Configuration=Release
if /I "%1"=="x86" set Platform=x86
if /I "%1"=="x64" set Platform=x64
if /I "%1"=="nosync" set NoSync=true
if /I "%1"=="clean" set CleanOnly=true
if /I "%1"=="noclean" set NoClean=true
if /I "%1"=="" goto :initsub
if /I "%1"=="/?" goto :help
if /I "%1"=="/h" goto :help
if /I "%1"=="/help" goto :help
if /I "%1"=="help" goto :help
shift
goto :parseargs

:initsub
if exist "P\README.md" goto :updatesub

echo ### Initializing your submodules 
git submodule init
git submodule update

:checksubmodule
for /f "usebackq tokens=1,2*" %%i in (`git submodule summary %1`) do (
  if "%%j"=="%1" echo #### Submodule is out of date: %1 & set SubmoduleOutOfDate=true  
)

goto :eof

:updatesub
if "%NoSync%"=="true" goto :nosync

echo ### Updating your submodules 
call :checksubmodule Ext/Formula
call :checksubmodule Ext/Zing

if "%SubmoduleOutOfDate%"=="false" goto :nosync

:sync
echo ### Fixing your submodules so they are up to date...
git submodule sync --recursive
git submodule update --init --recursive
goto :nosync

:nosync

echo "Building P..."
cd P\Bld
call build.bat %1 %2 %3 %4 


echo "Building Corral..."