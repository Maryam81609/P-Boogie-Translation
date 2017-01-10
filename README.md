# P-Boogie-Translation

Translates a given P file to a Boogie file.

### Usage
~~~
PBoogieTranslator.exe file.p [options]
	/deSugar
	/removeNT
	/removeSE
	/serialize
	/noBoogie
We will save to file with names like deSugared_file.p, NTRemoved_file.p, etc.
Other options:
	/list
		This option will consider the lines of the input file as file paths.
	/test
		This option will consider the lines of the input file as file paths, and run corral on each output.
	/genTestOutputs
		This option will consider the lines of the input file as file paths,
		and record corral outputs in a format similar to the Regression Tests.
	testAll
		This option will run all Regression Tests.

CreateCSV.exe file.txt
	Here, file.txt contains the list of all test cases to generate a CSV for. 

~~~

### Building
	Run build.bat

### TBD
	Add support for newer features of P - we use a version of P which is quite old - including InterfaceTypes, Enums, Module system declarations. 
	Add tech report.
	Generate Golden Outputs for the  tests in Tst/RegressionTests/Integration
	Improve/find the recursion bounds and context switch bounds.

