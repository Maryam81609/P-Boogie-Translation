# P-Boogie-Translation
Translates a given P file to a Boogie file.

~~~
 USAGE: PBoogieTranslator.exe file.p [options]
  OPTIONS:
        /deSugar:[name]?
        /outputFileName:[name]?
        /removeNT:[name]?
        /removeSE:[name]?
        /serialize:[name]?
        If name is not supplied, we will save to file with name like deSugared_file.p, NTRemoved_file.p, etc.
        If name is "-", output is printed to the terminal.
~~~
