using System;
using System.Collections.Generic;

using Microsoft.P2Boogie;
using Microsoft.FSharp.Collections;

namespace Microsoft.PBoogieTranslator
{
    class SymbolTable
    {
        private Stack<Tuple<string, Dictionary<string, Syntax.Type>>> tbls =
            new Stack<Tuple<string, Dictionary<string, Syntax.Type>>>();
        private Dictionary<string, Dictionary<string, Syntax.Type>> machinesToVars =
            new Dictionary<string, Dictionary<string, Syntax.Type>>();
        private Dictionary<string, HashSet<string>> machinesToFuns =
            new Dictionary<string, HashSet<string>>();
        public Dictionary<string, Dictionary<string, string>> machTrueNames =
            new Dictionary<string, Dictionary<string, string>>();
        private Stack<Dictionary<string, string>> trueNames = 
            new Stack<Dictionary<string, string>>();
        

        public string currentM { get; set; }
        public string currentF { get { if (tbls.Count > 0) return (tbls.Peek().Item1); else return null; } }
        public bool InsideStaticFn { get; set; } = false;
        
        public void NewScope(string name)
        {
            tbls.Push(new Tuple<string, Dictionary<string, Syntax.Type>>(name, new Dictionary<string, Syntax.Type>()));
            trueNames.Push(new Dictionary<string, string>());
        }

        public void ExitScope()
        {
            tbls.Pop();
            trueNames.Pop();
        }

        public void Clear()
        {
            tbls.Clear();
            machinesToVars.Clear();
            machinesToFuns.Clear();
            currentM = null;
            InsideStaticFn = false;
        }

        public string GetVarName(string x)
        {
            foreach (var tbl in tbls)
            {
                if (!InsideStaticFn && tbl.Item2.ContainsKey(x))
                    return tbl.Item1 + "_" + x;
            }

            if (!InsideStaticFn && machinesToVars[currentM].ContainsKey(x))
                return currentM + "_" + x;

            foreach (var tbl in tbls)
            {
                if (InsideStaticFn && tbl.Item2.ContainsKey(x))
                    return tbl.Item1 + "_" + x;
            }
            //throw new KeyNotFoundException("No such variable as " + x + " in scope!");
            return x; //Needed for expressions in global scope, like events.
        }

        public string GetFunName(string f)
        {
            if(!InsideStaticFn && machinesToFuns[currentM].Contains(f))
                return currentM + '_' + f;
            return f;
        }

        public Tuple<Syntax.Type.Tuple, Syntax.Expr.Tuple, 
            List<Syntax.VarDecl>, List<Syntax.Stmt>> IncludeSurroundingScopes(string fName)
        {
            var typLst = new List<Syntax.Type>();
            var expLst = new List<Syntax.Expr>();
            var vdLst = new List<Syntax.VarDecl>();
            //var asgnLst = new List<Syntax.Stmt>();
            var restoreLst = new List<Syntax.Stmt>();
            int i = 0;
            foreach (var tbl in tbls)
            {
                foreach(var v in tbl.Item2)
                {
                    var name = tbl.Item1 + '_' + v.Key;
                    typLst.Add(v.Value);
                    expLst.Add(Syntax.Expr.NewVar(name));
                    vdLst.Add(new Syntax.VarDecl(name, v.Value));
                    //asgnLst.Add(Syntax.Stmt.NewAssign(
                        //Syntax.Lval.NewDot(Syntax.Lval.NewVar(fName + "_env"), i), 
                        //Syntax.Expr.NewVar(name)));
                    restoreLst.Add(Syntax.Stmt.NewAssign(Syntax.Lval.NewVar(name),
                        Syntax.Expr.NewDot(Syntax.Expr.NewVar(fName + "_env"), i)));
                    i++;
                }
            }

            var tupType = Syntax.Type.NewTuple(ListModule.OfSeq(typLst)) 
                as Syntax.Type.Tuple;
            var tupExpr = Syntax.Expr.NewTuple(ListModule.OfSeq(expLst)) 
                as Syntax.Expr.Tuple;
            return new Tuple<Syntax.Type.Tuple, Syntax.Expr.Tuple, 
                List<Syntax.VarDecl>, List<Syntax.Stmt>>
                (tupType, tupExpr, vdLst, restoreLst);
        }

        public void AddMachine(string m)
        {
            if (!machinesToVars.ContainsKey(m))
                machinesToVars[m] = new Dictionary<string, Syntax.Type>();
            else
                throw new Exception("Machine " + m + "already exists!");

            if (!machinesToFuns.ContainsKey(m))
                machinesToFuns[m] = new HashSet<string>();
            else
                throw new Exception("Machine " + m + "already exists!");
            if (!machTrueNames.ContainsKey(m))
                machTrueNames[m] = new Dictionary<string, string>();
            else
                throw new Exception("Machine " + m + "already exists!");
        }

        public void AddMachVar(string m, string v, Syntax.Type t)
        {
            if (!machinesToVars.ContainsKey(m))
                throw new Exception("No such machine as " + m);
            machinesToVars[m].Add(v, t);
            machTrueNames[m].Add(m + "_" + v, v);
        }

        public void AddMachFun(string m, string f)
        {
            if (!machinesToFuns.ContainsKey(m))
                throw new Exception("No such machine as " + m);
            machinesToFuns[m].Add(f);
        }

        public void AddVar(string v, Syntax.Type t)
        {
            var tbl = tbls.Peek();
            tbl.Item2.Add(v, t);
            trueNames.Peek().Add(currentF + "_" + v, v);
        }

        public Dictionary<string, string> getTrueNamesInScope()
        {
            Dictionary<string, string> ret;
            if (!InsideStaticFn)
                ret = new Dictionary<string, string>(machTrueNames[currentM]);
            else
                ret = new Dictionary<string, string>();

            var arr = trueNames.ToArray();

            for(int i = arr.Length - 1; i >= 0; --i)
            {
                foreach(var kv in arr[i])
                {
                    ret[kv.Key] = kv.Value;
                }
            }            
            return ret;
        }

    }
}
