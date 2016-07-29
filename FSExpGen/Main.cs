using Microsoft.Pc;
using System;
using System.IO;
using Microsoft.P2Boogie;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Formatters.Binary;

namespace Microsoft.P_FS_Boogie
{
    class Program
    {
        public static int Main(string[] args)
        {
            CommandLineOptions options = new CommandLineOptions();
            FSharpExpGen fsExpGen = new FSharpExpGen(options);
            string line = null;
            int t = 0;
            int w = 0;
            using (var sr = new StreamReader(args[0]))
            {
                Syntax.ProgramDecl prog = null;
                while ((line = sr.ReadLine()) != null)
                {
                    if (line.StartsWith("//"))
                        continue;

                    Console.WriteLine("*****************************************************************************");
                    Console.WriteLine(line);
                    Console.WriteLine("*****************************************************************************");
                    using (var sw = new StreamWriter(line))
                    {
                        try
                        {
                            prog = fsExpGen.genFSExpression(line + ".txt");
                            prog = RemoveNamedTuples.removeNamedTuplesProgram (prog);
                            prog = RemoveSideEffects.removeSideEffectsProgram(prog);
                            Save(prog, line + ".dat"); //Debug
                            ProgramTyping.typecheckProgram(prog);
                            Helper.printProg(prog, sw);
                        }
                        
                        catch (Exception e)
                        {
                            w++;
                            Console.WriteLine(e.Message);
                            Console.WriteLine("\n\n");
                            Console.WriteLine(e.StackTrace);
                        }

                        finally
                        {
                            t++;
                        }
                    }
                }
            }
            Console.WriteLine("Passed {0} tests out of {1}.", t - w, t);
            return w;
        }

        static void Save(Syntax.ProgramDecl prog, string fileName)
        {
            Stream stream = null;
            try
            {
                IFormatter formatter = new BinaryFormatter();
                stream = new FileStream(fileName, FileMode.Create, FileAccess.Write, FileShare.None);
                formatter.Serialize(stream, prog);
            }
            catch
            {
                // do nothing, just ignore any possible errors
            }
            finally
            {
                if (null != stream)
                    stream.Close();
            }
        }
    }
}