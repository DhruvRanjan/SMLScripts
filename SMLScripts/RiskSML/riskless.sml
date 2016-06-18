functor Riskless(Dim : MAP) : GAME
    where type move = int * int =
struct
    open Seq
    exception IllegalState
    type vertex = int
    datatype player = Minnie | Maxie
    datatype outcome = Winner of player
    datatype status = Over of outcome | In_play

    datatype position = Min of int | Max of int | Empty

    structure Est = Estimate

    (* The string is simply there to give every territory a name *)
    datatype territory = T of string * position

    datatype gstate = B of (territory * vertex seq) seq * player * int
    type state = gstate

    type move = vertex * vertex

    fun move_to_string (i, j) =
        (Int.toString i) ^ " " ^ (Int.toString j)

    fun territory_to_string (i, (T (n, p))) =
        (Int.toString i) ^ ": " ^ n ^ "-- " ^
        (case p of
           Min (v) => "Minnie (" ^ (Int.toString v) ^ ")"
         | Max (v) => "Maxie  (" ^ (Int.toString v) ^ ")"
         | _ => "Unclaimed")

    fun neighbors_to_string (B (ts, _, _)) ss =
        mapreduce (fn i => let val (T (st, _), _) = nth i ts
                           in "\t" ^ (Int.toString i) ^ ": " ^ st
                           end) ""
                           (fn (a, b) => a ^ "\n" ^ b) ss

    (* Format: valid_move (state,move) *)
    fun valid_move (B(G,p,_),(s, t)) =
        let
          val (T(_,pos),S) = nth s G
          val (T(_,tgt),_) = nth t G
          val pres = mapreduce (fn x => x = t) false
                               (fn (a, b) => a orelse b) S
        in
          case (pos,tgt) of
            (Max(_),_) => (s <> t) andalso (p = Maxie) andalso pres
          | (Min(_),_) => (s <> t) andalso (p = Minnie) andalso pres
          | _ => false
        end

    fun parse_move state s =
        case String.tokens (fn #" " => true | _ => false) s of
            [si, sj] =>
              (case (Int.fromString si, Int.fromString sj) of
                   (SOME i, SOME j) =>
                       if valid_move (state,(i, j))
                       then SOME (i, j)
                       else NONE
                 | (_, _) => NONE)
          | _ => NONE

    fun pos_to_string (T (s, Empty), _) = s ^ ":"
      | pos_to_string (T (s, Min(i)), _) = s ^ ": O(" ^ (Int.toString i) ^ ")"
      | pos_to_string (T (s, Max(i)), _) = s ^ ": X(" ^ (Int.toString i) ^ ")"

    fun state_to_string (board as (B (ts, _, trn))) =
        "[TURN #" ^ (Int.toString trn) ^ "]\n" ^ Dim.board_to_string (map pos_to_string ts)

    (* creates the starting state *)
    val start : state = B(tabulate(fn a =>
       let
         val (x,y) = nth(a)(Dim.board)
       in
         if a=Dim.max_start then (T(x,Max(1)),y)
         else if a=Dim.min_start then (T(x,Min(2)),y)
         else (T(x,Empty),y)
       end)(length(Dim.board)),Maxie,1)

    (* status : state -> status *)
    (* REQUIRES : true *)
    (* ENSURES : status s evaluates to the current state of the game
     (in_play, or Winner(Minnie), or Winner(Maxie) *)
    fun status (state as B(graph,p,t)) =
     let
       val max_nodes = filter(fn c=>
         case c of
           T(_,Max(x))=>true
           | _ => false)
       (map(fn(a,b)=>a)(graph))
       val min_nodes = filter(fn d=>
         case d of
           T(_,Min(x))=>true
           | _ => false)
       (map(fn(a,b)=>a)(graph))
       val max_armies = mapreduce(fn T(a,b)=>
         case b of
          Max(x)=>x
          | _ => 0)(0)(op +)(max_nodes)
       val min_armies = mapreduce(fn T(a,b)=>
         case b of
          Min(x)=>x
          | _ => 0)(0)(op +)(min_nodes)
      in
     if length(max_nodes) = 0 then Over(Winner(Minnie))
     else if length(min_nodes) = 0 then Over(Winner(Maxie))
     else if max_armies > Dim.max_units orelse min_armies > Dim.max_units
     then
         (if max_armies > min_armies then
            Over(Winner(Maxie))
          else if min_armies > max_armies then
            Over(Winner(Minnie))
         else Over(Winner(p)))
     else if t = Dim.max_turns then
          (if max_armies > min_armies then
            Over(Winner(Maxie))
           else Over(Winner(Minnie)))
     else
       In_play
     end
    (* turn : state -> int *)
    (* REQUIRES : true *)
    (* ENSURES : turn s evaluates to the number of turns that have
       elapsed *)
    fun turn (state as B(graph,s,t)) = t

    (* moves : state -> move Seq.seq *)
    (* REQUIRES : true *)
    (* ENSURES : moves s evaluates to a sequence of valid moves for the
      state s. If there are no valid moves, it evaluates to an
       empty sequence *)

    fun moves (state as B(graph,s,t)) =
     if status(B(graph,s,t)) = In_play then
      let
       val nodes = tabulate(fn a => (a,nth(a)(graph)))(length(graph))
       val rel_nodes = filter(fn (_,(T(_,p),_))=>
         if s=Minnie then (case p of Min(x)=>true | _ => false)
         else if s=Maxie then (case p of Max(x)=>true | _ => false)
         else false)(nodes)
       val index_v = map(fn (i,(T(_,_),v))=> (i,v))(rel_nodes)
      in
      flatten(map(fn (a,b) => map(fn c => (a,c))(b))(index_v))
      end
     else empty()

    (* player : state -> player *)
    (* REQUIRES : true *)
    (* ENSURES : player s evaluates to the current player making the
       move in the current state s *)

    fun player (state as B(graph,s,t)) = s

    (* make_move : (state * move) -> state *)
    (* REQUIRES : true *)
    (* ENSURES : make_move (s,m) evaluates to the state after the move m
       has been applied *)

    fun make_move ((state as B(graph,cur_plr,t)), (i,j)) =
     let
      val (T(s,p), current_vec) = nth(i)(graph)
      val current_pos = p
      val (T(s2,p2), other_vec) = nth(j)(graph)
      val other_pos = p2
      val new_current_pos = case current_pos of
                              Max(x)=>Max(0)
                            | _ => Min(0)
      val new_other_pos = case other_pos of
           Max(x)=> (case current_pos of
                       Max(y) => Max(x+y)
                     | Min(z) => (case x>z of
                                    true => Max(x-z)
                                  | _ => Min(z-x)))
         | Min(x)=> (case current_pos of
                       Min(y) => Min(x+y)
                     | Max(z) => (case x>z of
                                    true => Min(x-z)
                                  | _ => Max(z-x)))
         | Empty => (case current_pos of
                       Max(y) => Max(y)
                     | Min(z) => Min(z))
      val new_graph =
         tabulate(fn a => case a=i of
                     true => (T(s,new_current_pos),current_vec)
                    | _ => (case a=j of
                        true => (T(s2,new_other_pos),other_vec)
                       | _ => nth(a)(graph)))(length(graph))
      val new_graph_plus1 = map(fn (T(s,p),v)=>case p of
                                   Max(x)=>(case x>=10 of
                                          true => (T(s,Max(10)),v)
                                         | _ =>(T(s,Max(x+1)),v))
                                 | Min(x)=>(case x>=10 of
                                          true => (T(s,Min(10)),v)
                                         | _ => (T(s,Min(x+1)),v))
                                 | _ => (T(s,Empty),v))(new_graph)
      val new_current_player = case cur_plr of
                     Maxie => Minnie
                  | _ => Maxie
      val turns_plus_one = t+1
     in
      B(new_graph_plus1,new_current_player,turns_plus_one)
     end


    type est = Est.est

    (* estimate : state -> Est.est *)
    (* REQUIRES : true *)
    (* ENSURES : estimate estimate s evaluates to an estimated score for
       the given state s *)

    fun estimate (state as B(graph,s,t)) =
     let
      val max_nodes = filter(fn c=>
         case c of
           T(_,Max(x))=>true
           | _ => false)
       (map(fn(a,b)=>a)(graph))
       val min_nodes = filter(fn d=>
         case d of
           T(_,Min(x))=>true
           | _ => false)
       (map(fn(a,b)=>a)(graph))
       val max_armies = mapreduce(fn T(a,b)=>
         case b of
          Max(x)=>x
          | _ => 0)(0)(op +)(max_nodes)
       val min_armies = mapreduce(fn T(a,b)=>
         case b of
          Min(x)=>x
          | _ => 0)(0)(op +)(min_nodes)
      in
        case s of
         Maxie => Est.Value(max_armies*length(max_nodes))
        | _ => Est.Value(~min_armies*length(min_nodes))
      end

    val mapID = Dim.mapID

end

(* Build Riskless game for each map *)
structure RL1 = Riskless (M1(P))
structure RL2 = Riskless (M2)

structure TestRiskless =
struct
  open RL1
  open Seq

  (* Checks for sequence equality *)
  fun seqEq f (a, b) =
      length a = length b andalso
      mapreduce f true (fn (a,b) => a andalso b) (zip (a,b))

  (* Converts list to sequence *)
  fun % nil = empty ()
    | % (x::L) = cons (singleton x) (% L)

end
