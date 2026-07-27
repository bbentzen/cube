(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Eager evaluation with full β-reduction on redexes of all types,
 *       η-reduction for dependent functions and paths,
 *       but not ε-reduction (i0/i1 endpoints) for dependent paths.
 **)

open Substitution

let rec eval = function

  | Ast.Coe (i, j, Ast.Abs(k, Pi(x, ty1, ty2)), e) ->  
    let v1 = fresh_var (Pi(x, ty1, ty2)) e 2 in
    let i' = eval i in
    let j' = eval j in
    let c x = Ast.Coe (j', x, Ast.Abs(k, ty1), Id v1) in
    Ast.Abs(v1, Ast.Coe (i', j', Ast.Abs(k, eval (subst x (c (Id k)) ty2)), eval (Ast.App(e, c i'))))
  
  | Ast.Coe (i, j, Ast.Abs(k, Sigma(x, ty1, ty2)), e) ->
    let i' = eval i in
    let j' = eval j in
    let c x = Ast.Coe (i', x, Ast.Abs(k, ty1), Ast.Fst e) in
    Ast.Pair(c j', Ast.Coe (i', j', Ast.Abs(k, eval (subst x (c (Id k)) ty2)), Ast.Snd (eval e)))

  | Ast.Coe (i, j, Ast.Abs(k, Pathd(ty, e1, e2)), e) ->
      let v1 = fresh_var (Ast.App(e1, e2)) e 2 in
      let v2 = fresh_var (Ast.App(e1, e2)) e 3 in
      let i' = eval i in
      let j' = eval j in
      Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
      Ast.Abs(v1, Ast.Coe (i', j', (Ast.Abs(k, (eval (Ast.App(ty, Id v1))))), eval (Ast.At(e, Ast.Id v1)))), 
      Ast.Abs(v2, Ast.Coe (Id v2, j', (Ast.Abs(k, (eval (Ast.App(ty, I0()))))), eval (subst k (Id v2) e1))),
      Ast.Abs(v2, Ast.Coe (Id v2, j', (Ast.Abs(k, (eval (Ast.App(ty, I1()))))), eval (subst k (Id v2) e2)))),
      I1()), Id v1))

  | Ast.Coe (i, j, e1, e2) ->
    begin
      let i' = eval i in
      let j' = eval j in
      let e2' = eval e2 in
      if i' = j' then
        e2'
      else
        let e1' = eval e1 in
        match e1' with
        | Ast.Abs(k, e) ->
          if has_var k e then
            Ast.Coe (i', j', e1', e2')
          else
            e2'  (* coercion regularity *)
        | _ ->
          Ast.Coe (i', j', e1', e2')
    end
  
  | Ast.Hfill (e, e1, e2) ->
    let e' = eval e in
    let e1' = eval e1 in
    let e2' = eval e2 in
    Ast.Hfill (e', e1', e2')
  
  | Ast.App (Ast.Hfill (e, _, _), Ast.I0()) -> 
    eval e

  | Ast.App (Ast.App (Ast.Hfill (_, e1, _), i), Ast.I0()) -> 
    eval (Ast.App(e1, i))

  | Ast.App (Ast.App (Ast.Hfill (_, _, e2), i), Ast.I1()) -> 
    eval (Ast.App(e2, i))

  | Ast.Abs (x, e) -> 
    begin
      let e' = eval e in
      match e' with
      | Ast.App (e1 , e2) ->
        if e2 = Ast.Id x && not (has_var x e1) then 
          eval e1
        else
          Ast.Abs (x, e')
      | _ ->
        Ast.Abs (x, e')
    end

  | Ast.App (e1, e2) -> 
    begin
      let e1' = eval e1 in
      match e1' with
      | Ast.Abs (x , e) ->
        if Placeholder.has_underscore e then
          let e2' = eval e2 in
          Ast.App (e1', e2')
        else
          eval (subst x e2 e)
      | _ ->
        let e2' = eval e2 in
        Ast.App (e1', e2')
    end

  | Ast.Pair (e1, e2) ->
    begin
      let e1' = eval e1 in
      let e2' = eval e2 in
      match e1', e2' with
      | Ast.Fst e11, Ast.Snd e22 ->
        if e11 = e22 then
          eval e11
        else
          Ast.Pair (e1', e2')
      | _ ->
        Ast.Pair (e1', e2')
    end

  | Ast.Fst e ->
    begin
      let e' = eval e in
      match e' with
      | Ast.Pair (e1 , _) -> eval e1
      | _ -> 
        Ast.Fst e'
    end

  | Ast.Snd e -> 
    begin
      let e' = eval e in
      match e' with
      | Ast.Pair (_ , e2) -> eval e2
      | _ -> 
        Ast.Snd e'
    end

  | Ast.Inl e ->
    let e' = eval e in
    Ast.Inl e'

  | Ast.Inr e -> 
    let e' = eval e in
    Ast.Inr e'

  | Ast.Case (e, e1, e2) -> 
    begin
      let e' = eval e in
      match e' with
      | Ast.Inl a -> eval (Ast.App (e1,a))
      | Ast.Inr b -> eval (Ast.App (e2,b))
      | _ ->
        let e1' = eval e1 in
        let e2' = eval e2 in
        Ast.Case (e', e1', e2')
    end

  | Ast.Succ e ->
    let e' = eval e in
    Ast.Succ e'

  | Ast.Natrec (e, e1, e2) -> 
    begin
      let e' = eval e in 
      match e' with
      | Ast.Zero() -> eval e1
      | Ast.Succ k -> eval (Ast.App (Ast.App (e2,k),Ast.Natrec(k,e1,e2)))
      | _ -> 
        let e1' = eval e1 in
        let e2' = eval e2 in
        Ast.Natrec (e', e1', e2')
    end

  | Ast.If (e, e1, e2) -> 
    begin
      let e' = eval e in
      match e' with
      | Ast.True() -> eval e1
      | Ast.False() -> eval e2
      | _ ->
        let e1' = eval e1 in
        let e2' = eval e2 in
        Ast.If (e', e1', e2')
    end

  | Ast.Let (e, e1) -> 
    begin
      let e' = eval e in
      match e' with
      | Ast.Star() -> eval e1
      | _ -> 
        let e1' = eval e1 in
        Ast.Let (e', e1')
    end

  | Ast.Pabs (x, e) -> 
    begin
      let e' = eval e in
      match e' with
      | Ast.At (e1 , e2) ->
        if e2 = Ast.Id x && not (free_var x e1) then 
          eval e1
        else
          Ast.Pabs (x, e')
      | _ ->
        Ast.Pabs (x, e')
    end

  | Ast.At (e1, e2) -> 
    begin
      let e1' = eval e1 in
      match e1' with
      | Ast.Pabs (x , e) ->
        if Placeholder.has_underscore e then
          let e2' = eval e2 in
          Ast.At (e1', e2')
        else
          subst x e2 (eval e)
      | _ ->
        let e2' = eval e2 in
        Ast.At (e1', e2')
    end
  
  | Ast.Pi (x, e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
    Ast.Pi (x, e1', e2')

  | Ast.Sigma (x, e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
    Ast.Sigma (x, e1', e2')

  | Ast.Sum (e1, e2) ->
    let e1' = eval e1 in
    let e2' = eval e2 in
    Ast.Sum (e1', e2')

  | Ast.Pathd (e, e1, e2) -> 
    let e' = eval e in
    let e1' = eval e1 in
    let e2' = eval e2 in
    Ast.Pathd (e', e1', e2')

  | Ast.Type l ->
    Ast.Type (Universe.eval l)
    
  | e -> e