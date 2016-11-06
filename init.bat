@echo off
setlocal
pushd %~dp0

echo *****************************************************************************************************************
echo Updating your submodules
echo *****************************************************************************************************************
git submodule init 
git submodule sync
git submodule update


set Configuration=Debug
set Platform=x86

echo 
echo 
echo *****************************************************************************************************************
echo Building P...
echo *****************************************************************************************************************
cd P
git submodule init
git submodule update
cd ext\zing

echo msbuild  Zing.sln /p:Platform=%Platform% /p:Configuration=Release
msbuild  Zing.sln /p:Platform=%Platform% /p:Configuration=Release

set BinaryDrop=..\..\Bld\Drops\%Configuration%\%Platform%\Binaries
if NOT exist %BinaryDrop% mkdir %BinaryDrop%

for %%i in (zc\bin\%Platform%\Release\zc.exe
             ZingExplorer\bin\%Platform%\Release\ZingExplorer.dll
             Zinger\bin\%Platform%\Release\Zinger.exe
             Microsoft.Zing\bin\%Platform%\Release\Microsoft.Zing.dll
             Microsoft.Zing.Runtime\bin\%Platform%\Release\Microsoft.Zing.Runtime.dll
             Microsoft.Zing\bin\%Platform%\Release\Microsoft.Comega.dll
             Microsoft.Zing\bin\%Platform%\Release\Microsoft.Comega.Runtime.dll
             Resources\external\CCI\System.Compiler.dll
             Resources\external\CCI\System.Compiler.Framework.dll
             Resources\external\CCI\System.Compiler.Runtime.dll
             DelayingSchedulers\CustomDelayingScheduler\bin\%Platform%\Release\CustomDelayingScheduler.dll
             DelayingSchedulers\RandomDelayingScheduler\bin\%Platform%\Release\RandomDelayingScheduler.dll
             DelayingSchedulers\RoundRobinDelayingScheduler\bin\%Platform%\Release\RoundRobinDelayingScheduler.dll
             DelayingSchedulers\RunToCompletionDelayingScheduler\bin\%Platform%\Release\RunToCompletionDelayingScheduler.dll
	     DelayingSchedulers\SealingScheduler\bin\%Platform%\Release\SealingScheduler.dll) do (
             
    copy %%i %BinaryDrop%
)
   
cd ..\..
del Src\PrtDist\Core\NodeManager_c.c
del Src\PrtDist\Core\NodeManager_s.c

echo msbuild P.sln /p:Platform=%Platform% /p:Configuration=%Configuration%
msbuild  P.sln /p:Platform=%Platform% /p:Configuration=%Configuration% /t:Clean
 
cd ..
echo Done!

echo 
echo 
echo *****************************************************************************************************************
echo Building Corral...
echo *****************************************************************************************************************
cd corral
git submodule init
git submodule update
MSBuild cba.sln
cd ..
cp bin\z3.exe corral\bin\Debug\


popd

echo 
echo 
echo *****************************************************************************************************************
echo Init done. Now, build the translator from Visual Studio.
echo *****************************************************************************************************************
echo 
echo 
