namespace Microsoft.P2Boogie
module RemoveSideEffects = 
  open Syntax
  open Common
  open Helper
  open ProgramTyping

  /// Takes an expr as input, returns the re-written expr, a set of statements and updated environment 
  let rec removeSideEffectsExpr expr G =
    let (nexpr, stlist, nG) =
      match expr with
      | Nil
      | ConstInt _
      | ConstBool _
      | Event _
      | This
      | Expr.Var(_) -> (expr, [], G)
      | Expr.Default t when t = Int || t = Null || t = Bool || t = Any || t = Machine || t = Type.Event -> (expr, [], G)
      | Nondet -> 
        begin
          let (l, G') = getLocal Bool G in
          (Expr.Var(l), [Assign(Lval.Var(l), Nondet)], G')
        end
      | Bin(op, e1, e2) when (op = Eq || op = Neq) ->
        begin
          let (e1', s1, G') = removeSideEffectsExpr e1 G in
          let (e2', s2, G'') = removeSideEffectsExpr e2 G' in
          let (l, G''') = getLocal Bool G'' in
          let nexpr = if op = Eq then Expr.Var(l) else Expr.Un(Not, Expr.Var(l)) in
          (nexpr, s1 @ s2 @ [Assign(Lval.Var(l), Bin(Eq, e1', e2'))], G''')
        end
      | Bin(op, e1, e2) when op = In || op = Idx ->
        begin
          let (l, G') = getLocal (typeof expr G) G in
          let (e1', s1, G'') = removeSideEffectsExpr e1 G' in
          let (e2', s2, G''') = removeSideEffectsExpr e2 G'' in
          (Expr.Var(l), s1 @ s2 @ [Assign(Lval.Var(l), Bin(op, e1', e2'))], G''')
        end
      | Bin(op, e1, e2) ->
        begin
          let (e1', s1, G') = removeSideEffectsExpr e1 G in
          let (e2', s2, G'') = removeSideEffectsExpr e2 G' in
          (Bin(op, e1', e2'), s1 @ s2, G'')
        end
      | Un(Keys, e) ->
        begin
          let (l, G') = getLocal (Seq (getDomainType (typeof e G))) G in
          (Expr.Var(l), [Assign(Lval.Var(l), expr)], G')
        end
      | Un(Values, e) ->
        begin
          let (l, G') = getLocal (Seq (getRangeType (typeof e G))) G in
          (Expr.Var(l), [Assign(Lval.Var(l), expr)], G')
        end
      | Un(op, e) ->
        begin
          let (e', s, G') = removeSideEffectsExpr e G in
          (Un(op, e'), s, G')
        end
      | Expr.Dot(e,f) ->
        begin
          let (e', s, G') = removeSideEffectsExpr e G in
          (Expr.Dot(e', f), s, G')
        end
      | Expr.NamedTuple(_)
      | Expr.NamedDot(_, _) -> raise NotDefined
      | Expr.Default t ->
        begin
          let (l, G') = getLocal t G in
          match t with 
          | Type.Tuple(ts) ->
            begin
              let (a, b, c) = 
                List.fold (fun (partialLs, partialStlist, partialG) ti -> 
                  begin
                    let (li, G'') = getLocal ti partialG in
                    let (e', s, G''') = removeSideEffectsExpr (Expr.Default ti) G'' in
                    (li :: partialLs, partialStlist @ s @ [Assign(Lval.Var(li), e')], G''')
                  end
                  ) ([], [], G') ts
              in
              (Expr.Var(l), b @ [Assign(Lval.Var(l), Expr.Tuple (List.map Expr.Var (List.rev a)))], c)
            end
          | _ -> (Expr.Var(l), [Assign(Lval.Var(l), expr)], G')
        end      
      | Expr.Tuple(es) ->
        begin
          let (a, b, c) = 
            List.fold (fun (partialEs, partialStlist, partialG) e -> 
              begin
                let (e', s, G') = removeSideEffectsExpr e partialG in
                (e' :: partialEs, partialStlist @ s, G')
              end
              ) ([], [], G) es
          in
          let (l, Gfinal) = getLocal (typeof expr G) c in
          (Expr.Var(l), b @ [Assign(Lval.Var(l), Expr.Tuple(List.rev a))], Gfinal)
        end
      | Expr.Call(callee, es) ->
        begin
          let (a, b, c) = 
            List.fold (fun (partialEs, partialStlist, partialG) e -> 
              begin
                let (e', s, G') = removeSideEffectsExpr e partialG in
                (e' :: partialEs, partialStlist @ s, G')
              end
              ) ([], [], G) es
          in
          let (l, Gfinal) = getLocal (typeof expr G) c in
          (Expr.Var(l), b @ [Assign(Lval.Var(l), Expr.Call(callee, List.rev a))], Gfinal)
        end
      | New(m, e) ->
        begin
          let (e', s, G') = removeSideEffectsExpr e G in
          let (l, G'') = getLocal (typeof expr G') G' in
          (Expr.Var(l), s @ [Assign(Lval.Var(l), New(m, e'))], G'')
        end
      | Expr.Cast(e, t) when (isSubtype (typeof e G) t) -> 
        begin
          (* redundant cast *)
          removeSideEffectsExpr e G
        end
      | Expr.Cast(e, t) -> 
        begin
          let (e', s, G') = removeSideEffectsExpr e G in
          let (l, G'') = getLocal t G' in
          (Expr.Var(l), s @ [Assign(Lval.Var(l), Expr.Cast(e',t))], G'')
        end
      in (nexpr, stlist, nG) 

  let removeSideEffectsExprlist exprlist G = 
    List.fold (fun (partialExplist, partialStlist, partialG) expr ->
      begin
        let (e, d, G') = removeSideEffectsExpr expr partialG in
        (partialExplist @ [e], partialStlist @ d, G')
      end
      ) ([], [], G) exprlist

  /// returns a list of statements and a new G 
  let rec normalizeLvalStmt st G =
    match st with
    | Assign(lval, e) ->
      begin
        match lval with
            (*l.f = e
            * ==> 
            * l = (l.0, l.1, ..., e) *)
        | Lval.Dot(l, f) -> 
          begin
            let e', stlst, G' = 
              match e with
              | Tuple(ls) ->
                begin
                  let t, g = getLocal (typeof e G) G
                  let sl, g' = normalizeLvalStmt (Assign(Lval.Var(t), e)) g
                  Expr.Var(t), sl, g'
                end
              | _ -> e, [], G
            let t = tupleSize (typeofLval l G) in
            let rhs = ref [] in
            for i = (t-1) downto 0 do
              if i = f then rhs := e'::!rhs
              else rhs := Expr.Dot(lvalToExpr l, i) :: !rhs
            let sl', G'' = normalizeLvalStmt (Assign(l, Expr.Tuple !rhs)) G'
            stlst @ sl', G''
          end
        | Lval.Index(Lval.Var(_), _) -> ([st], G)
            (* l[e'] = e
            * ==> 
            * t = l; t[e'] = e; l = t
            *)
        | Lval.Index(l, e') ->
          begin
            let (t, G') = getLocal (typeofLval l G) G in
            let s1 = Assign(Lval.Var(t), lvalToExpr l) in
            let s2 = Assign(Lval.Index(Lval.Var(t), e'), e) in
            let s3 = Assign(l, Expr.Var(t)) in
            let (s3list, G'') = normalizeLvalStmt s3 G' in
            ([s1; s2] @ s3list, G'')
          end
        | _ -> ([st], G)
      end
    | Remove(lval, e) ->
      begin
        match lval with
        (* lval -= e
          * ==>
          * t = lval; t -= e; lval = t
          *)
        | Lval.Dot(_ ,_)
        | Lval.Index(_, _) ->
          begin
            let (t, G') = getLocal (typeofLval lval G) G in
            let s1 = Assign(Lval.Var(t), lvalToExpr lval) in
            let s2 = Remove(Lval.Var(t), e) in
            let s3 = Assign(lval, Expr.Var(t)) in
            let (s3list, G'') = normalizeLvalStmt s3 G' in
            ([s1; s2] @s3list, G'')
          end
        | _ -> ([st], G)
      end
    | Insert(lval, e1, e2) ->
      begin
        match lval with
        (* lval += (e1,e2)
          * ==>
          * t = lval; t += (e1,e2); lval = t
          *)
        | Lval.Dot(_, _) 
        | Lval.Index(_, _) ->
          begin
            let (t, G') = getLocal (typeofLval lval G) G in
            let s1 = Assign(Lval.Var(t), lvalToExpr lval) in
            let s2 = Insert(Lval.Var(t), e1, e2) in
            let s3 = Assign(lval, Expr.Var(t)) in
            let (s3list, G'') = normalizeLvalStmt s3 G' in
            ([s1; s2] @s3list, G'')
          end
        | _ -> ([st], G)
      end
    | _ -> ([st], G)

  /// returns new list of statements and the new G 
  let normalizeLvalStlist stlist G =
    List.fold (fun (partialStlist, partialG) stmt ->
      begin
        let (d, G') = normalizeLvalStmt stmt partialG in
        (partialStlist @ d, G')
      end
      ) ([], G) stlist
  
  let rec removeSideEffectsLval lval G = 
    match lval with
    | Lval.Var(v) -> lval, [], G
    | Lval.Dot(l, f) -> 
    begin
      let l', stl, G' = removeSideEffectsLval l G
      Lval.Dot(l', f), stl, G'
    end
    | Lval.Index(l, e) -> 
      begin
        let l', stl1, G' = removeSideEffectsLval l G
        let e', stl2, G'' = removeSideEffectsExpr e G'
        Lval.Index(l', e'), stl1 @ stl2, G''
      end
    | Lval.NamedDot(_) -> raise NotDefined

  let rec removeSideEffectsStmt stmt G =
    match stmt with
    | Assign(l, e) -> 
      begin
        let (l', d1, G')  = removeSideEffectsLval l G in
        let (e', d2, G'') = removeSideEffectsExpr e G' in
        let s = Assign(l', e') in
        let (d3, G''') = normalizeLvalStmt s G'' in
        (d1 @ d2 @ d3, G''')
      end
    | Insert(l, e1, e2) ->
      begin
        let (l', d1, G')  = removeSideEffectsLval l G in
        let (e1', d2, G'') = removeSideEffectsExpr e1 G' in
        let (e2', d3, G''') = removeSideEffectsExpr e2 G'' in
        let s = Insert(l', e1', e2') in 
        let (d4, G'''') = normalizeLvalStmt s G''' in 
        (d1 @ d2 @ d3 @ d4, G'''')
      end
    | Remove(l, e) ->
      begin
        let (l', d1, G')  = removeSideEffectsLval l G in
        let (e', d2, G'') = removeSideEffectsExpr e G' in
        let s = Remove(l', e') in
        let (d3, G''') = normalizeLvalStmt s G'' in
        (d1 @ d2 @ d3, G''')
      end
    | Assume(e) ->
      begin
        let (e', d, G') = removeSideEffectsExpr e G in
        (d @ [Assume(e')], G')
      end
    | Assert(e) -> 
      begin
        let (e', d, G') = removeSideEffectsExpr e G in
        (d @ [Assert(e')], G')
      end
    | NewStmt(_, Nil) -> [stmt], G
    | NewStmt(s, e)-> 
      begin
        let (e', d, G') = removeSideEffectsExpr e G in
        (d@[NewStmt(s, e')], G')
      end
    | Raise(e1, Nil) ->      
      begin
        let (e1', d, G') = removeSideEffectsExpr e1 G in
        (d@[Raise(e1', Nil)], G')
      end
    | Raise(e1, e2) ->
      begin
        let (e1', d1, G') = removeSideEffectsExpr e1 G in
          let (e2', d2, G'') = removeSideEffectsExpr e2 G' in 
            (d1 @ d2 @ [Raise(e1', e2')], G'')
      end
    | Send (e1, e2, Nil) ->
      begin
        let (e1', d1, G') = removeSideEffectsExpr e1 G in
          let (e2', d2, G'') = removeSideEffectsExpr e2 G' in 
            (d1 @ d2 @ [Send(e1', e2', Nil)], G'')
      end
    | Send (e1, e2, e3) ->
      begin
        let (e1', d1, G') = removeSideEffectsExpr e1 G in
          let (e2', d2, G'') = removeSideEffectsExpr e2 G' in 
            let (e3', d3, G''') = removeSideEffectsExpr e3 G'' in 
            (d1 @ d2 @ d3 @ [Send(e1', e2', e3')], G''')
      end
    | Skip(_) -> [stmt], G
    | While(c, s) -> 
      begin
        let (c', d1, G') = removeSideEffectsExpr c G in
          let (d2, G'') = removeSideEffectsStmt s G' in 
            d1 @ [While(c', SeqStmt(d2 @ d1))], G'' 
      end
    | Ite(c, i, e) -> 
       begin
        let (c', d1, G') = removeSideEffectsExpr c G in
          let (d2, G'') = removeSideEffectsStmt i G' in 
            let (d3, G''') = removeSideEffectsStmt e G'' in 
              d1 @ [Ite(c', SeqStmt(d2), SeqStmt(d3))], G'''
      end
    | SeqStmt(l) -> removeSideEffectsStlist l G
    | Receive(_) -> [stmt], G
    | Pop -> [stmt], G
    | Return(None) -> [stmt], G
    | Return(Some(e)) -> 
      begin
        let (e', d, G') = removeSideEffectsExpr e G in 
          d @ [Return(Some(e'))], G'
      end
    | Monitor(e1, e2) -> 
      begin
        let (e1', d1, G') = removeSideEffectsExpr e1 G in
          let (e2', d2, G'') = removeSideEffectsExpr e2 G' in 
            (d1 @ d2 @ [Monitor(e1', e2')], G'')
      end
    | FunStmt(s, el, v) -> 
      begin
        let v' = 
          match v, (Map.find s G) with
          | None, typ when typ <> Type.Null -> Some("tmpRhsValue")
          | _ -> v
        let (el', d, G') = removeSideEffectsExprlist el G in
          d @ [FunStmt(s, el', v')], G'
      end
    | Goto(s, e) -> 
      begin
        let (e', d, G') = removeSideEffectsExpr e G in
          d @ [Goto(s, e')], G'
      end

  /// returns new list of statements and the new G 
  and removeSideEffectsStlist stlist G =
    List.fold (fun (partialStlist, partialG) stmt ->
      begin
        let (d, G') = removeSideEffectsStmt stmt partialG in
        (partialStlist @ d, G')
      end
      ) ([], G) stlist

  ///Get Defaults for each variable declared. Returns a set of statements and an updated environment.
  let getDefaults (vdList: VarDecl list) G = 
    let defs = List.fold (fun ls (vd: VarDecl) -> ls @ [Stmt.Assign(Lval.Var(vd.Name), Expr.Default(vd.Type))]) [] vdList
    removeSideEffectsStlist defs G

  ///Get all the vars in G2 that are not present in G1.
  let getNewVars G1 G2 = 
    let g1 = G1 |> Map.toSeq |> Seq.map fst |> Set.ofSeq
    let g2 = G2 |> Map.toSeq |> Seq.map fst |> Set.ofSeq
    let newVars = Set.difference g2 g1
    [for x in newVars do yield new VarDecl(x, (Map.find x G2))]
  
  ///Return a new FunDecl with all statements causing 
  ///only one side effect at most.
  let removeSideEffectsFn G (f: FunDecl) = 
    let G' = mergeMaps G f.VarMap
    let defs, G'' = getDefaults f.Locals G'
    let stList, G''' = removeSideEffectsStlist f.Body G''
    let newVars = f.Locals @ (getNewVars G' G''')
    new FunDecl(f.Name, f.Formals, f.RetType, newVars, defs @ stList, f.IsModel, f.IsPure, f.TrueNames)

  ///Return a new MachineDecl with all statements 
  ///causing only one side effect at most.
  let removeSideEffectsMachine G (m:MachineDecl) = 
    let funs = 
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) m.Functions
      !map  
    let G' = mergeMaps (mergeMaps G m.VarMap) funs
    let init, G'' = getDefaults m.Globals G'
    let newGlobals = m.Globals @ (getNewVars G' G'')
    let fList = List.map (removeSideEffectsFn G'') m.Functions 
    new MachineDecl(m.Name, m.StartState, newGlobals , fList, m.States, m.IsMonitor, m.MonitorList, m.QC, m.IsModel, m.HasPush, init)

  ///Return a new ProgramDecl with all statements causing 
  ///only one side effect at most.
  let removeSideEffectsProgram (prog: ProgramDecl) = 
    let G =           
      let map = ref Map.empty in
        List.iter (fun(f: FunDecl) -> map := Map.add f.Name (if f.RetType.IsSome then f.RetType.Value else Type.Null) !map) prog.StaticFuns
      !map 
    let mList = List.map (removeSideEffectsMachine G) prog.Machines
    let fList = List.map (removeSideEffectsFn G) prog.StaticFuns
    new ProgramDecl(mList, prog.Events, prog.EventsToMonitors, fList, prog.maxFields, prog.HasDefer, prog.HasIgnore)
