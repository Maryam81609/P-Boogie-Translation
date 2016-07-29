namespace Microsoft.P2Boogie
module Main = 
  open System.Runtime.Serialization
  open System.Runtime.Serialization.Formatters
  open System.Runtime.Serialization.Formatters.Binary
  open System.IO
  open System

  open Syntax
  open Helper
  open ProgramTyping
  open RemoveSideEffects
  open Translator
  open System.CodeDom.Compiler
  
  let getProgram pFile = 
    begin
      let formatter = new BinaryFormatter()
      let fileName = (sprintf "%s.dat" pFile)
      let stream = new FileStream(fileName, FileMode.Open, FileAccess.Read, FileShare.None)
      formatter.Deserialize(stream) :?> Syntax.ProgramDecl
    end
  let printProgram (pFile: string) = 
    begin
      
      System.Console.WriteLine("*****************************************************************************");
      System.Console.WriteLine(pFile);
      let prog = getProgram pFile
      let OpFile = new System.IO.StreamWriter(pFile)
      printProg prog OpFile
      OpFile.Close()
    end


  [<EntryPoint>]
  let main argv = 
    use t = new StreamWriter(argv.[1])
    //let t = System.Console.Out
    let sw = new IndentedTextWriter(t, "   ") 
    translateProg (getProgram argv.[0]) sw
    //File.ReadLines(argv.[0]) |> Seq.iter (printProgram)
(*
    let file = @"C:\Users\t-suchav\P\Tst\RegressionTests\Feature1SMLevelDecls\Correct\PingPong\PingPong.p"
    let prog = removeSideEffectsProgram (getProgram file) 
    let opFile = new System.IO.StreamWriter(@"C:\Users\t-suchav\Desktop\recv12.p")
    printProg prog opFile
    printProg prog System.Console.Out
    typecheckProgram prog
*)
  

