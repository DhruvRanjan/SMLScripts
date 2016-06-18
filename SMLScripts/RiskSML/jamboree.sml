functor Jamboree (Settings : sig
                                 structure G : GAME
                                 val search_depth : int
                                 val prune_percentage : real
                             end) : PLAYER  =
struct
  structure Game = Settings.G

  type edge = (Game.move * Game.est)

  datatype value =
           BestEdge of edge
         | Pruned

  datatype result =
           Value of value
         | ParentPrune   (* an evaluation result *)

  type alphabeta = value * value (* invariant: alpha < beta *)

  (* the following ToString functions my be helpful in testing *)
  fun valueToString (v : value) : string =
      case v of
        Pruned => "Pruned"
      | BestEdge (_,e) => "Value(" ^ Game.Est.toString e ^ ")"

  fun resultToString r =
      case r of Value v => valueToString v | ParentPrune => "ParentPrune"

  fun abToString (a,b) = "(" ^ valueToString a ^ "," ^ valueToString b ^ ")"

  fun lt (x,y) = case Game.Est.compare(x,y) of
                   LESS => true
                 | _ => false

  (* for alpha, we want max(alpha,Pruned) to be alpha, i.e.
     Pruned <= alpha for any alpha;
     otherwise order by the estimates on the edges
     *)
  fun alpha_is_less_than (alpha : value, v : Game.est) : bool =
      case alpha of
          Pruned => true
        | BestEdge(_,alphav) => lt(alphav,v)

  fun maxalpha (v1,v2) : value =
      case (v1,v2) of
          (Pruned,y) => y
        | (x,Pruned) => x
        | (BestEdge(_,e1), BestEdge(_,e2)) =>
          case lt (e1,e2) of true => v2 | false => v1

  (* for beta, we want min(beta,Pruned) to be beta, i.e.
     beta <= Pruned for any beta;
     otherwise order by the estimates on the edges
     *)
  fun beta_is_greater_than (v : Game.est, beta : value) : bool =
      case beta of
          Pruned => true
        | BestEdge(_,betav) => lt(v,betav)
  fun minbeta (v1,v2) : value =
      case (v1,v2) of
          (Pruned,y) => y
        | (x,Pruned) => x
        | (BestEdge(_,e1), BestEdge(_,e2)) =>
          case lt (e1,e2) of true => v1 | false => v2

  fun updateAB (state : Game.state)
               ((alpha, beta) : alphabeta)
               (value : value) : alphabeta =
     let
       val new_ab = case Game.player(state) of
        Game.Maxie => (maxalpha(alpha,value), beta)
       | _ => (alpha,minbeta(beta,value))
     in
        new_ab
     end

  fun value_for (state : Game.state)
                ((alpha, beta) : alphabeta) : value =
     case Game.player(state) of
        Game.Maxie => alpha
          | _ => beta

 fun check_bounds ((alpha,beta) : alphabeta)
                   (state : Game.state)
                   (incomingMove : Game.move)
                   (v : Game.est) : result =
     if alpha_is_less_than(alpha,v) andalso beta_is_greater_than(v,beta)
       then
     Value(BestEdge(incomingMove,v))
     else if alpha_is_less_than(alpha,v)=false then
        (if Game.player(state)=Game.Maxie then ParentPrune
         else Value(Pruned))
     else if Game.player(state)=Game.Maxie then Value(Pruned)
     else ParentPrune

  (* splitMoves : Game.state -> (Game.move Seq.seq, Game.move Seq.seq) *)
  (* REQUIRES : true *)
  (* ENSURES : splitMoves s evaluates to two sequence (a,b) given a game
     state s depending on the prune_percentage *)

  fun splitMoves s =
      let
       val moves = Game.moves(s)
       val length = Seq.length moves
       val pp = Real.floor(Settings.prune_percentage*Real.fromInt(length))
     in
       Seq.split pp moves
     end

   fun vmax (v1, v2) : Game.est =
        case Game.Est.compare (v1, v2) of
          LESS => v2
        | _ => v1

    fun vmin (v1, v2) : Game.est =
        case Game.Est.compare (v1, v2) of
          GREATER => v2
        | _ => v1

   fun value_eq (v1,v2) =
      case (v1,v2) of
         (BestEdge(_,e1), BestEdge(_,e2)) =>
              Game.Est.compare(e1,e2) = EQUAL
     | _ => false

   fun vmax2 ((mv1 : Game.move, r1),(mv2, r2)) =
      case ((mv1,r1),(mv2,r2)) of
         ((mv1, Value(x)),(mv2, Value(y))) => (case
                       value_eq(maxalpha(x,y),x) of
                         true => (mv1, Value(x))
                       | _ => (mv2, Value(y)))
        | _ => (mv1, r1)

    fun vmin2 ((mv1 : Game.move, r1),(mv2, r2)) =
      case ((mv1,r1),(mv2,r2)) of
         ((mv1, Value(x)),(mv2, Value(y))) => (case
                      value_eq(minbeta(x,y),x) of
                         true => (mv1, Value(x))
                       | _ => (mv2, Value(y)))
        | _ => (mv1, r1)

  fun evaluate (depth : int)
               (ab : alphabeta)
               (state : Game.state)
               (incomingMove : Game.move) : result =
     if depth=0 orelse (not(Game.status(state)=Game.In_play)) then
        check_bounds(ab)(state)(incomingMove)(Game.estimate(state))
     else
       let
         val (abmoves, mmmoves) = splitMoves(state)
       in
         Value(search(depth)(ab)(state)(abmoves)(mmmoves))
       end

  and search (depth : int)
             (ab : alphabeta)
             (state : Game.state)
             (abmoves : Game.move Seq.seq)
             (mmmoves : Game.move Seq.seq) : value =
      case Seq.length(abmoves) of
         0 => let
                val mm = case Game.player state of
            Game.Minnie =>
            SeqUtils.reduce1 vmin2
                   (Seq.map (fn mv => (mv,evaluate(depth - 1)(ab)
                         (Game.make_move(state,mv))(mv)))
                                      (mmmoves))
          | Game.Maxie =>
            SeqUtils.reduce1 vmax2
                            (Seq.map (fn mv => (mv,evaluate(depth - 1)(ab)
                            (Game.make_move(state,mv))(mv)))
                                      (mmmoves))
                val abv = value_for(state)(ab)
               in
                 case mm of
                  (m,ParentPrune) => abv
                | (m,Value(Pruned)) => abv
                | (m,Value(BestEdge(m2,e2))) => (case abv of
                              Pruned => BestEdge(m2,e2)
                    | BestEdge(m1,e1) => (case Game.player(state) of
                        Game.Maxie => maxalpha(BestEdge(m2,e2),
                                               BestEdge(m1,e1))
                       | _ => minbeta(BestEdge(m2,e2),BestEdge(m1,e1))))

        end
      | _ =>
          let
            val current_move = Seq.nth(0)(abmoves)
            val child_result = evaluate(depth-1)(ab)
                    (Game.make_move(state,current_move))(current_move)
          in
            case child_result of
              ParentPrune => Pruned
            | Value(x) => search(depth)(updateAB(state)(ab)(x))(state)
                        (Seq.drop(1)(abmoves))(mmmoves)
          end


  exception no_move

  fun next_move s =
   let
    val (abmoves,mmmoves) = splitMoves s
    val move = search(Settings.search_depth)((Pruned,Pruned))(s)
              (abmoves)(mmmoves)
   in
    case move of
     (BestEdge(x,e))=> x
    | _ => raise no_move
   end


end
