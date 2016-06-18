functor AlphaBeta (Settings : sig
                                  structure G : GAME
                                  val search_depth : int
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

  (* For alpha, we want max(alpha,Pruned) to be alpha, i.e.
   * Pruned <= alpha for any alpha;
   * otherwise order by the estimates on the edges *)
  fun alpha_is_less_than (alpha : value, v : Game.est) : bool =
      case alpha of
          Pruned => true
        | BestEdge(_,alphav) => Game.Est.compare(alphav,v) = LESS
  fun maxalpha (v1,v2) : value =
      case (v1,v2) of
          (Pruned,y) => y
        | (x,Pruned) => x
        | (BestEdge(_,e1), BestEdge(_,e2)) =>
              case Game.Est.compare(e1,e2) of LESS => v2 | _ => v1

  (* For beta, we want min(beta,Pruned) to be beta, i.e.
   * beta <= Pruned for any beta;
   * otherwise order by the estimates on the edges *)
  fun beta_is_greater_than (v : Game.est, beta : value) : bool =
      case beta of
          Pruned => true
        | BestEdge(_,betav) => Game.Est.compare(v,betav) = LESS
  fun minbeta (v1,v2) : value =
      case (v1,v2) of
          (Pruned,y) => y
        | (x,Pruned) => x
        | (BestEdge(_,e1), BestEdge(_,e2)) =>
              case Game.Est.compare(e1,e2) of LESS => v1 | _ => v2

  (* updateAB : Game.state -> alphabeta -> value -> alphabeta *)
  (* REQUIRES : true *)
  (* ENSURES : updateAB s ab v updates the appropriate on of ab with the
       new value v *)
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
  (* value_for : Game.state -> alphabeta -> value *)
  (* REQUIRES : true *)
  (* ENSURES : value_for s ab evaluates to the appropriate one of ab for
     the player whose turn it is in s *)

  fun value_for (state : Game.state)
                ((alpha, beta) : alphabeta) : value =
     case Game.player(state) of
        Game.Maxie => alpha
          | _ => beta

  (* check_bounds : alphabeta -> Game.state -> Game.move -> Game.est ->
                    result *)
  (* REQUIRES : true *)
  (* ENSURES : check_bounds ab s m v evaluates to the appropiate result
        according to the spec for ab pruning, given the candidate value
        v *)

  fun check_bounds ((alpha,beta) : alphabeta)
                   (state : Game.state)
                   (incomingMove : Game.move)
                   (v : Game.est) : result =
     if alpha_is_less_than(alpha,v) andalso
     beta_is_greater_than(v,beta) then
     Value(BestEdge(incomingMove,v))
     else if alpha_is_less_than(alpha,v)=false then
        (if Game.player(state)=Game.Maxie then ParentPrune
         else Value(Pruned))
     else if Game.player(state)=Game.Maxie then Value(Pruned)
     else ParentPrune

  (* evaluates : int -> alphabeta -> Game.state -> Game.move -> result *)
  (* REQUIRES : true *)
  (* ENSURES : evaluate i ab s m checks if the boundary conditions
     are met and if they are not, then calls search *)

  fun evaluate (depth : int)
               (ab : alphabeta)
               (state : Game.state)
               (incomingMove : Game.move) : result =
      if depth=0 orelse (not(Game.status(state)=Game.In_play)) then
        check_bounds(ab)(state)(incomingMove)(Game.estimate(state))
      else Value(search(depth)(ab)(state)(Game.moves(state)))

  (* search : int -> alphabeta -> Game.state -> Game.move Seq.seq ->
             value *)
  (* REQUIRES : depth is not zero, state is In_play and moves is a
             sequence of valid moves for s *)
  (* ENSURES : search i ab s ms evaluates the children of s given
     by the moves in ms and returns the appropriate value
     for the parent s *)

  and search (depth : int)
             ((a,b) : alphabeta)
             (state : Game.state)
             (moves : Game.move Seq.seq) =
      case Seq.length(moves) of
        0 => value_for(state)((a,b))
      | _ =>
        let
          val current_move = Seq.nth(0)(moves)
          val child_result = evaluate(depth-1)((a,b))(Game.make_move
             (state,current_move))(current_move)
        in
         case child_result of
          ParentPrune => Pruned
        | Value(x) => search(depth)(updateAB(state)((a,b))(x))(state)
                     (Seq.drop(1)(moves))
        end

  exception no_move

  (* next_move : state -> Game.move *)
  (* REQUIRES : true *)
  (* ENSURES : next_move s evaluates to the next move to be done given a
     state s *)

  fun next_move s =
   let
    val move = search(Settings.search_depth)((Pruned,Pruned))
              (s)(Game.moves(s))
   in
    case move of
        BestEdge(x,e)=> x
    | _ => raise no_move
   end

end
