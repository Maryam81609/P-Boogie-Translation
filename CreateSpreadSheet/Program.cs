using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Office.Interop.Excel;
using System.IO;

namespace CreateSpreadSheet
{
    class Program
    {
        static void Main(string[] args)
        {
            var xlApp = new Application();
            if (xlApp == null)
            {
                Console.WriteLine("Excel is not properly installed!");
                return;
            }

            xlApp.Workbooks.Open(@"..\..\..\status.xlsx", 0, false, 5, "", "", true, XlPlatform.xlWindows, "\t", true, false, 0, true, 1, 0);

            string file = "";
            int count = 1;
            using (var sr = new StreamReader(args[0]))
            {
                while ((file = sr.ReadLine()) != null)
                {
                    if (file.StartsWith("//"))
                        continue;
                    count++;
                    var dir = Path.GetDirectoryName(file);
                    var stat = Path.Combine(dir, "corral", "stat.txt");
                    using (var st = new StreamReader(stat))
                    {
                        string line = "";
                        double boogieVerTime, ioTime, progCheckTime, pathCheckTime, totalTime, cpuTime;
                        int procInlined, varTracked;
                        while ((line = st.ReadLine()) != null)
                        {
                            var dat = line.Split(':');
                            if (line.StartsWith("Boogie verification time"))
                            {
                                double.TryParse(dat[1].Substring(0, dat[1].Length - 2), out boogieVerTime);
                            }
                            else if (line.StartsWith("Time spent reading-writing programs"))
                            {
                                double.TryParse(dat[1].Substring(0, dat[1].Length - 2), out ioTime);
                            }
                            else if (line.StartsWith("Time spent checking a program"))
                            {
                                double.TryParse(dat[1].Substring(0, dat[1].Length - 2), out progCheckTime);
                            }
                            else if (line.StartsWith("Time spent checking a path"))
                            {
                                double.TryParse(dat[1].Substring(0, dat[1].Length - 2), out pathCheckTime);
                            }
                            else if (line.StartsWith("Number of procedures inlined"))
                            {
                                int.TryParse(dat[1], out procInlined);
                            }
                            else if (line.StartsWith("Number of variables tracked"))
                            {
                                int.TryParse(dat[1], out varTracked);
                            }
                            else if (line.StartsWith("Total Time"))
                            {
                                double.TryParse(dat[1].Substring(0, dat[1].Length - 2), out totalTime);
                            }
                            else if (line.StartsWith("Total User CPU time"))
                            {
                                double.TryParse(dat[1].Substring(0, dat[1].Length - 2), out cpuTime);
                            }
                        }
                    }

                    var op = Path.Combine(dir, "corral", "op.txt");

                    using (var st = new StreamReader(op))
                    {
                        var l = 0;
                        var line = "";
                        var f = Path.GetFileName(file);
                        while ((line = st.ReadLine()) != null)
                        {
                            if (line.StartsWith(f))
                            {
                                line = line.Substring(f.Length + 1, line.IndexOf(','));
                                int.TryParse(line, out l);
                                break;
                            }
                        }
                    }

                    var options = Path.Combine(dir, "corral", "options.txt");

                    using (var st = new StreamReader(options))
                    {
                        var rb = 0;
                        var k = 0;
                        var line = st.ReadLine().Split();
                        foreach (var x in line)
                        {
                            if (x.StartsWith("/recursionBound:"))
                            {
                                int.TryParse(x.Substring(16), out rb);
                            }
                            else if (x.StartsWith("/k:"))
                            {
                                int.TryParse(x.Substring(3), out k);
                            }
                        }
                    }
                }
            }
        }
    }
}
