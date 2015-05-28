structure Syntax : ABT_UTIL =
struct
  structure V = StringVariable
  structure Abt = Abt
    (structure Operator = Operator
     structure Variable = V)

  structure MyOp = Operator
  structure AbtUtil = AbtUtil(Abt)
  open AbtUtil

  local
    infix $ \
    infix 8 $$ // \\
    open MyOp
  in
    fun to_string pm =
    let
      fun enclose E =
        case out E of
             ` x => display E
           | O $ #[] => display E
           | _ => "(" ^ display E ^ ")"

      and display E =
        case out E of
             ISECT $ #[A,xB] =>
               let
                 val (x, B) = unbind xB
               in
                 "⋂" ^ Variable.to_string pm x ^ " ∈ " ^ display A ^ ". " ^ display B
               end

           | FUN $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "Π" ^ Variable.to_string pm x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " => " ^ display B
               end

           | PROD $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "Σ" ^ Variable.to_string pm x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " × " ^ display B
               end

           | LAM $ #[xE] =>
               let
                 val (x, E) = unbind xE
               in
                 "λ" ^ dvar (x, E) ^ ". " ^ display E
               end

           | AP $ #[M, N] =>
               enclose M ^ "[" ^ display N ^ "]"

           | PAIR $ #[M, N] =>
               "⟨" ^ display M ^ ", " ^ display N ^ "⟩"

           | SQUASH $ #[A] =>
               "‖" ^ display A ^ "‖"

           | MEM $ #[M, A] =>
               display M ^ " ∈ " ^ display A

           | EQ $ #[M, N, A] =>
               display M ^ " = " ^ display N ^ " ∈ " ^ display A

           | UNIV i $ #[] =>
               "U" ^ subscript i

           | SPREAD $ #[M, xyN] =>
               let
                 val (x, yN) = unbind xyN
                 val (y, N) = unbind yN
               in
                 "let " ^ dvar (x, yN) ^ "," ^ dvar (y, N) ^ " = " ^ display M ^ " in " ^ display N
               end

           | UNIT_INTRO $ #[] =>
              "⬧"

           | PROD_EQ $ #[D, xE] =>
               let
                 val (x, E) = unbind xE
               in
                 if has_free (E, x) then
                   "Σ⁼" ^ Variable.to_string pm x ^ " ∈ " ^ display D ^ ". " ^ display E
                 else
                   enclose D ^ " ×⁼ " ^ display E
               end

           | PROD_INTRO $ #[M, D, E] =>
               "⟨⸤" ^ display M ^ "⸥ by " ^ display D ^ ", " ^ display E ^ "⟩"

           | PROD_ELIM $ #[D, xyE] =>
               let
                 val (x, yE) = unbind xyE
                 val (y, E) = unbind yE
               in
                 "let " ^ dvar (x, yE) ^ "," ^ dvar (y, E) ^ " = " ^ display D ^ " in " ^ display E
               end

           | SPREAD_EQ $ #[D, xyE] =>
               let
                 val (x, yE) = unbind xyE
                 val (y, E) = unbind yE
               in
                 "let⁼ " ^ dvar (x, yE) ^ "," ^ dvar (y, E) ^ " = " ^ display D ^ " in " ^ display E
               end

           | SQUASH_INTRO $ #[M] =>
               "[" ^ display M ^ "]"

           | FUN_EQ $ #[D, xE] =>
               let
                 val (x, E) = unbind xE
               in
                 if has_free (E, x) then
                   "Π⁼" ^ Variable.to_string pm x ^ " ∈ " ^ display D ^ ". " ^ display E
                 else
                   enclose D ^ " =>⁼ " ^ display E
               end

           | FUN_INTRO $ #[xD, E] =>
               let
                 val (x, D) = unbind xD
               in
                 "λ" ^ dvar (x, D) ^ " ∈ " ^ display E ^ ". " ^ display D
               end

           | FUN_ELIM $ #[f, s, D, yzE] =>
               let
                 val (y, zE) = unbind yzE
                 val (z, E) = unbind zE
               in
                 "let " ^ dvar (y, zE) ^ " = " ^ enclose f ^ "[" ^ display s ^ " : " ^ display D ^ "] by " ^ dvar (z, E) ^ " in " ^ display E
               end

           | LAM_EQ $ #[xD, E] =>
               let
                 val (x, D) = unbind xD
               in
                 "λ⁼" ^ dvar (x, D) ^ " ∈ " ^ display E ^ ". " ^ display D
               end

           | AP_EQ $ #[D, E] =>
               display D ^ "[" ^ display E ^ "]⁼"

           | ISECT_INTRO $ #[xD, E] =>
               let
                 val (x, D) = unbind xD
               in
                 "λ[" ^ dvar (x, D) ^ " ∈ " ^ display E ^ "]. " ^ display D
               end

           | VOID_ELIM $ #[D] =>
               "!" ^ display D

           | HYP_EQ $ #[x] =>
               display x ^ "⁼"

           | REWRITE_EQ $ #[D, E] =>
               "rewrite " ^ display D ^ " in " ^ display E

           | WITNESS $ #[M, D] =>
               "⸤" ^ display M ^ "⸥ by " ^ display D

           | CUM $ #[D] =>
               "cumulativity " ^ display D

           | _ =>
               to_string_open to_string pm E

      and dvar (x, E) =
        if has_free (E, x) then Variable.to_string pm x else "_"

      and subscript i =
        case i of
             0 => "₀"
           | 1 => "₁"
           | 2 => "₂"
           | 3 => "₃"
           | 4 => "₄"
           | 5 => "₅"
           | 6 => "₆"
           | 7 => "₇"
           | 8 => "₈"
           | 9 => "₉"
           | _ => let val m = i mod 10 in subscript ((i - m) div 10) ^ subscript m end
    in
      display
    end
  end
end
