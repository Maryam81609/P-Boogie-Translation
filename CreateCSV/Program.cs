using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace CreateCSV
{
    class Program
    {
        static void Main(string[] args)
        {
            string file = "";
            int count = 0;
            Console.WriteLine("Serial No., File, Failed Assert Line Number, Recursion Bound, Context Bound, "
               + "Verification Time, IO Time, Time Spent Checking a Program,"
               + "Time Spent Checking a Path, Procedures Inlined, Variables Tracked, Total Time, CPU Time");
            using (var sr = new StreamReader(args[0]))
            {
                while ((file = sr.ReadLine()) != null)
                {
                    try
                    {
                        if (file.StartsWith("//"))
                            file = file.Substring(2);
                        count++;
                        var dir = Path.GetDirectoryName(file);
                        Console.Write("{0}, {1}, ", count, file);

                        var op = Path.Combine(dir, "corral", "op.txt");

                        using (var st = new StreamReader(op))
                        {
                            var line = "";
                            var f = Path.GetFileName(file);
                            var flag = false;
                            while ((line = st.ReadLine()) != null)
                            {
                                if (line.StartsWith(f))
                                {
                                    Console.Write("{0}, ", line.Substring(f.Length + 1, line.IndexOf(',')));
                                    flag = true;
                                    break;
                                }
                                if(!flag)
                                {
                                    Console.Write("NA, ");
                                }
                            }
                        }

                        var options = Path.Combine(dir, "corral", "options.txt");

                        using (var st = new StreamReader(options))
                        {
                            var line = st.ReadLine().Split();
                            foreach (var x in line)
                            {
                                if (x.StartsWith("/recursionBound:"))
                                {
                                    Console.Write("{0}, ", x.Substring(16));
                                }
                                else if (x.StartsWith("/k:"))
                                {
                                    Console.Write("{0}, ", x.Substring(3));
                                }
                            }
                        }

                        var stat = Path.Combine(dir, "corral", "stat.txt");
                        using (var st = new StreamReader(stat))
                        {
                            string line = "";
                            while ((line = st.ReadLine()) != null)
                            {
                                var dat = line.Split(':');
                                if (line.StartsWith("Boogie verification time"))
                                {
                                    Console.Write("{0}, ", dat[1].Substring(0, dat[1].Length - 2));
                                }
                                else if (line.StartsWith("Time spent reading-writing programs"))
                                {
                                    Console.Write("{0}, ", dat[1].Substring(0, dat[1].Length - 2));
                                }
                                else if (line.StartsWith("Time spent checking a program"))
                                {
                                    Console.Write("{0}, ", dat[1].Substring(0, dat[1].Length - 2));
                                }
                                else if (line.StartsWith("Time spent checking a path"))
                                {
                                    Console.Write("{0}, ", dat[1].Substring(0, dat[1].Length - 2));
                                }
                                else if (line.StartsWith("Number of procedures inlined"))
                                {
                                    Console.Write("{0}, ", dat[1]);
                                }
                                else if (line.StartsWith("Number of variables tracked"))
                                {
                                    Console.Write("{0}, ", dat[1]);
                                }
                                else if (line.StartsWith("Total Time"))
                                {
                                    Console.Write("{0}, ", dat[1].Substring(0, dat[1].Length - 2));
                                }
                                else if (line.StartsWith("Total User CPU time"))
                                {
                                    Console.WriteLine("{0}, ", dat[1].Substring(0, dat[1].Length - 2));
                                }
                            }
                        }
                    } catch(Exception e)
                    {
                        Console.WriteLine();
                        continue;
                    }
                }

            }
        }
    }
}
