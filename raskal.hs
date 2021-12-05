-- :set -XRecordWildCards
{-# LANGUAGE RecordWildCards #-}

import System.Environment
import Control.Exception
import Data.Char
import Debug.Trace


data Ras_Error =
  Illformed_Declarement
  | Tycon_mismatched
  | Symbol_notdefined
  | Symbol_redifinition
  | Typedef_no_synon_name
  | Typedef_no_synon_type
  | Typedef_invalid_synon_type
  | Typedef_redefinition
  | Typedef_illformed_declarement
  | Decl_illegal_construct
  | Expr_illformed_subexpr
  | Expr_illegal_expression
  | Expr_illegal_operation
  | Expr_no_valid_lvalue
  | Expr_no_valid_rvalue
  | Expr_parentheses_mismatched
  | Expr_has_no_effect
  | Compiler_internal_error
  deriving (Eq, Ord, Show)

data Ras_compiling_err =
  Par_error ((Int, Int), Ras_Error)
  | Typ_error ((Int, Int), Ras_Error)
  deriving (Eq, Ord, Show)


ras_trace str expr =
  let suppress = True
  in
    if not suppress then (trace str expr) else expr


ras_assert cond expr =
  let elim = False
  in
    if not elim then (assert cond expr) else expr


add_error errors err =
  case errors of
    Nothing -> Just [err]
    Just es -> Just (es ++ [err])

append_error err1 err2 =
  case err1 of
    Nothing -> err2
    Just es1 -> (case err2 of
                   Nothing -> err1
                   Just es2 -> Just (es1 ++ es2) )


--type Ras_typedef_attr = ((Int, Int), String, Ras_Types)
data Ras_typedef_attr0 = Ras_typedef_attr0 {tydef_coord :: (Int, Int), tydef_ident :: String, tydef_deftype :: Ras_Types}
  deriving (Eq, Ord, Show)

data Ras_Record_field =
  Ras_Record_field {memb_coord :: (Int, Int), memb_ident :: String, memb_type :: Ras_Types}
  deriving (Eq, Ord, Show)

type Ras_Record_attr = ((Int, Int), String, [Ras_Record_field])

data Ras_Types =
  Ras_Top_type
  | Ras_Boolean
  | Ras_Integer
  | Ras_Real
  | Ras_String
  | Ras_Char
  | Ras_Record Ras_Record_attr
  | Ras_Typedef Ras_typedef_attr0
  | Ras_Bottom_type
  | Ras_Unknown_type
  | Ras_Illformed_type
  deriving (Eq, Ord, Show)


data Boolean_const =
  Ras_Boolean_const Bool
  deriving (Eq, Ord, Show)

data Char_const =
  Ras_Char_const Char
  deriving (Eq, Ord, Show)

data String_const =
  Ras_String_const String
  deriving (Eq, Ord, Show)

data Numeric_const =
  Ras_Integer_const Int
  | Ras_Real_const (Int, Int)
  deriving (Eq, Ord, Show)

data Record_const =
  Ras_Record_const Ras_Types
  deriving (Eq, Ord, Show)

data Ras_Const =
  Boolean_const Boolean_const
  | Char_const Char_const
  | String_const String_const
  | Numeric_const Numeric_const
  | Record_const Record_const
  | Ras_Const_not_defined
  deriving (Eq, Ord, Show)


data Token_codes =
  AND
  | ARRAY
  | BEGIN | BOOLEAN
  | CASE | CHAR | CONST
  | DIV | DO | DOWNTO
  | ELSE | END
  | FALSE | FILE | FOR | FUNCTION
  | GOTO
  | IF | IN | INTEGER
  | LABEL
  | MOD
  | NIL | NOT
  | OF | OR
  | PACKED | PROCEDURE | PROGRAM | PERCENT
  | REAL | RECORD | REPEAT
  | SET
  | TRUE | THEN | TO | TYPE
  | UNTIL
  | VAR
  | WHILE | WITH
  | COMMA
  | COLON
  | DOT
  | EQU
  | CROSS
  | INCL
  | MINUS
  | DECL
  | STAR | STRING | SLASH
  | LBRA
  | RBRA
  | LPAR
  | RPAR
  | SEMICOL
  | ASGN
  | TYPED_AS
  | DEF
  | IDENT String
  | BOOL_CONST Boolean_const
  | NUM_CONST Numeric_const
  | CHR_CONST Char_const
  | STR_CONST String_const
  | SKIPPED String
  | PHONY
  | EOT  -- End of Tokens
  deriving (Eq, Ord, Show)


lex_main lexicon (row, col) src =
  ras_trace "in lex_main" (
  let coding tk_buf cand (row, col) src =
        let delimiter c = (c /= '_') && not (isAlphaNum c)
            elim c cand' =
              case cand' of
                [] -> []
                ((substr, tk_code):cs) -> (case substr of
                                             [] -> []
                                             (c':cs') -> if c' == c then [(cs', tk_code)] else []) ++ (elim c cs)
        in
          case src of
            [] -> (tk_buf, lookup "" cand, (row, col), [])
            (c:cs) | delimiter c -> (tk_buf, lookup "" cand, (row, col), src)
                   | otherwise -> coding (tk_buf ++ [c]) (elim c cand) (row, col + 1) cs
  in
    case src of
      [] -> []
      (c:cs) | c == '\n' -> lex_main lexicon (row + 1, 0) cs
             | c == '{' -> ((row, col), LBRA):(lex_main lexicon (row, col + 1) cs)
             | c == '}' -> ((row, col), RBRA):(lex_main lexicon (row, col + 1) cs)
             | c == '(' -> ((row, col), LPAR):(lex_main lexicon (row, col + 1) cs)
             | c == ')' -> ((row, col), RPAR):(lex_main lexicon (row, col + 1) cs)
             | (c == ' ' || c == '\t') -> lex_main lexicon (row, col + 1) cs
             | c == '=' -> (case cs of
                              '=':cs' -> ((row, col), EQU):(lex_main lexicon (row, col + 2) cs')
                              _ -> ((row, col), ASGN):(lex_main lexicon (row, col + 1) cs)
                           )
             | c == ':' -> (case cs of
                              ':':cs' -> ((row, col), TYPED_AS):(lex_main lexicon (row, col + 2) cs')
                              '=':cs' -> ((row, col), DEF):(lex_main lexicon (row, col + 2) cs')
                              _ -> ((row, col), COLON):(lex_main lexicon (row, col + 1) cs)
                           )
             | c == ';' -> ((row, col), SEMICOL):(lex_main lexicon (row, col + 1) cs)
             | c == ',' -> ((row, col), COMMA):(lex_main lexicon (row, col + 1) cs)
             | c == '.' -> ((row, col), DOT):(lex_main lexicon (row, col + 1) cs)
             | c == '+' -> (case cs of
                              c':cs'
                                | c' == '+' -> ((row, col), INCL):(lex_main lexicon (row, col + 2) cs')
                                | (isDigit c') -> lex_const ( par_num_const (False, ((ord c') - (ord '0'))) ) (row, col + 2) cs'
                                | otherwise -> ((row, col), CROSS):(lex_main lexicon (row, col + 1) cs)
                              _ -> ((row, col), CROSS):(lex_main lexicon (row, col + 1) cs)
                           )
             | c == '-' -> (case cs of
                              c':cs'
                                | c' == '-' -> ((row, col), DECL):(lex_main lexicon (row, col + 2) cs')
                                | (isDigit c') -> lex_const ( par_num_const (True, (negate ((ord c') - (ord '0')))) ) (row, col + 2) cs'
                                | otherwise -> ((row, col), MINUS):(lex_main lexicon (row, col + 1) cs)
                              _ -> ((row, col), MINUS):(lex_main lexicon (row, col + 1) cs)
                           )
             | c == '*' -> ((row, col), STAR):(lex_main lexicon (row, col + 1) cs)
             | c == '/' -> ((row, col), SLASH):(lex_main lexicon (row, col + 1) cs)
             | c == '\'' -> lex_const par_chr_const (row, col + 1) cs
             | c == '"' -> lex_const par_str_const (row, col + 1) cs
             | (isDigit c) -> lex_const ( par_num_const (False, ((ord c) - (ord '0'))) ) (row, col + 1) cs
             | otherwise -> (case (coding "" lexicon (row, col) src) of
                               (tk_str, res, (row', col'), rem) -> (case res of
                                                                      Just tk_code ->
                                                                        if (tk_code == TRUE) then [((row, col), BOOL_CONST (Ras_Boolean_const True))]
                                                                        else if (tk_code == FALSE) then [((row, col), BOOL_CONST (Ras_Boolean_const False))]
                                                                             else [((row, col), tk_code)]
                                                                      Nothing -> [((row, col), IDENT tk_str)]
                                                                   ) ++ (lex_main lexicon (row', col') rem)
                            )
      
        where
          lex_const method (row, col) src = case (method (row, col) src) of
                                              (tk_code, (row', col'), rem) -> [((row, col - 1), tk_code)] ++ (lex_main lexicon (row', col') rem)
          
          par_chr_const (row, col) src = case src of
                                           [] -> (SKIPPED "'", (row, col), [])
                                           (ch:cs') -> (case cs' of
                                                          (c':rem) | c' == '\'' -> (CHR_CONST (Ras_Char_const ch), (row, col + 3), rem)
                                                                   | otherwise -> (SKIPPED "'",(row, col + 2),  src)
                                                          _ -> (SKIPPED "'", (row, col + 2), src) )
          
          par_str_const (row, col) src =
            let acc_chr buf (row, col) src =
                  case src of
                    [] -> (False, buf, (row, col), [])
                    (ch:cs) | ch == '"' -> (True, buf, (row, col + 1), cs)
                            | otherwise -> acc_chr (buf ++ [ch]) (row, col + 1) cs
            in
              case src of
                [] -> (SKIPPED "\"", (row, col), [])
                _ -> (case (acc_chr "" (row, col) src) of
                        (res, str, (row', col'), rem) -> if res then (STR_CONST (Ras_String_const str), (row', col'), rem)
                                                         else (SKIPPED "\"", (row', col'), src) )

          par_num_const (neg, acc) (row, col) src = let sign = if neg then negate else id
                                                    in
                                                      case src of
                                                        [] -> (NUM_CONST (Ras_Integer_const acc), (row, col), [])
                                                        (c':cs') | (isDigit c') -> (par_num_const (neg, ((acc * 10) + (sign ((ord c') - (ord '0'))))) (row, col + 1) cs')
                                                                 | otherwise -> (NUM_CONST (Ras_Integer_const acc), (row, col), src)
  )

lex src =
    let lexicon = [("and", AND), ("array", ARRAY),
                   ("begin", BEGIN), ("boolean", BOOLEAN),
                   ("case", CASE), ("char", CHAR), ("const", CONST),
                   ("div", DIV), ("do", DO), ("downto", DOWNTO),
                   ("else", ELSE), ("end", END),
                   ("false", FALSE), ("file", FILE), ("for", FOR), ("function", FUNCTION),
                   ("goto", GOTO),
                   ("if", IF), ("in", IN), ("integer", INTEGER),
                   ("label", LABEL),
                   ("mod", MOD),
                   ("nil", NIL), ("not", NOT),
                   ("of", OF), ("or", OR),
                   ("packed", PACKED), ("procedure", PROCEDURE), ("program", PROGRAM),
                   ("real", REAL), ("record", RECORD), ("real", REAL), ("repeat", REPEAT),
                   ("set", SET), ("string", STRING),
                   ("then", THEN), ("to", TO), ("true", TRUE), ("type", TYPE),
                   ("until", UNTIL),
                   ("var", VAR),
                   ("while", WHILE), ("with", WITH)]
    in
      lex_main lexicon (1, 1) src
  

par_real_const tk_past tokens =
  ras_trace "in par_real_const" (
  let is_valid tk = case tk of
                      (_, PHONY) -> []
                      _ -> [tk]
  in
    case tokens of
      [] -> is_valid tk_past
      ((r, c), DOT):t':ts' ->
        (case t' of
           (_, NUM_CONST (Ras_Integer_const lt0)) ->
             (case tk_past of
                ((r_p, c_p), NUM_CONST (Ras_Integer_const gte0)) -> ((r_p, c_p), NUM_CONST (Ras_Real_const (gte0, lt0))):(par_real_const ((-1, -1), PHONY) ts')
                _ -> (is_valid tk_past) ++ (((r, c), DOT):(par_real_const t' ts'))
             )
           _ -> (is_valid tk_past) ++  (((r,c), DOT):[t']) ++ (par_real_const ((-1, -1), PHONY) ts')
        )
      (t:ts) -> (is_valid tk_past) ++ (par_real_const t ts)
  )


data Mediate_code_mnemonic =
  Mn_asgn
  | Mn_add
  | Mn_sub
  | Mn_mul
  | Mn_div
  | Mn_mod
  | Mn_neg
  | Mn_preinc
  | Mn_pstinc
  | Mn_predec
  | Mn_pstdec
  | Mn_prec
  | Mn_nop
  | Mn_unknown
  deriving (Eq, Ord, Show)

data Mediate_var_attr =
  Mediate_var_attr {var_coord :: (Int, Int), var_ident :: String, var_type :: Ras_Types, var_attr :: Mediate_var_attr}
  | Var_attr_const ((Int, Int), Ras_Const)
  | Var_attr_fields [Mediate_code_fragment_raw]
  | Var_attr_none
  deriving (Eq, Ord, Show)

data Mediate_code_fragment_raw =
  Mediate_code_raw_typedef Ras_typedef_attr0
  | Mediate_code_raw_Literal ((Int, Int), Ras_Const)
  | Mediate_code_raw_Var Mediate_var_attr
  | Mediate_code_raw_Par {mnemonic :: ((Int, Int), Mediate_code_mnemonic), operand_0 :: Mediate_code_fragment_raw}
  | Mediate_code_raw_Una {mnemonic :: ((Int, Int), Mediate_code_mnemonic), operand_0 ::  Mediate_code_fragment_raw}
  | Mediate_code_raw_Bin {mnemonic :: ((Int, Int), Mediate_code_mnemonic), operand_0 :: Mediate_code_fragment_raw, operand_1 :: Mediate_code_fragment_raw}
  -- | Mediate_code_raw_typedef {tydef_coord :: (Int, Int), tydef_ident :: String, tydef_deftype :: Ras_Types}
  | Mediate_code_fragment_raw_None ((Int, Int), Token_codes)
  deriving (Eq, Ord, Show)


is_subtype ty1 ty2 = {- returns True if ty1 <: ty2, otherwise False. -}
  ras_trace "in is_subtype" (
  case ty2 of
    Ras_Top_type -> True
    Ras_Boolean -> (ty1 == Ras_Boolean) || (ty1 == Ras_Bottom_type)
    Ras_Integer -> (ty1 == Ras_Integer) || (ty1 == Ras_Bottom_type)
    Ras_Real -> (ty1 == Ras_Real) || (ty1 == Ras_Integer) || (ty1 == Ras_Bottom_type)
    Ras_String -> (ty1 == Ras_String) || (ty1 == Ras_Char) || (ty1 == Ras_Bottom_type)
    Ras_Char -> (ty1 == Ras_Char) || (ty1 == Ras_Bottom_type)
    Ras_Bottom_type -> (ty1 == Ras_Bottom_type)
    _ -> False
  )

tyinf expr = {- obtaining the type of expr, with type inference. -}
  ras_trace "in tyinf" (
  case expr of
    Mediate_code_raw_Par {mnemonic = (pos_m, m)} -> if (m == Mn_prec) then (tyinf (operand_0 expr))
                                                    else
                                                      ras_assert False (Ras_Unknown_type, Just [Typ_error(pos_m, Expr_illegal_operation)])
    Mediate_code_raw_Literal (pos,c) -> (case c of
                                           Boolean_const c' -> (Ras_Boolean, Nothing)
                                           Char_const c' -> (Ras_Char, Nothing)
                                           String_const c' -> (Ras_String, Nothing)
                                           Numeric_const c' -> (case c' of
                                                                  Ras_Integer_const c_i -> (Ras_Integer, Nothing)
                                                                  Ras_Real_const c_r -> (Ras_Real, Nothing)
                                                                  _ -> ras_assert False (Ras_Unknown_type, Just [Typ_error(pos, Tycon_mismatched)])
                                                               )
                                           Record_const _ -> (Ras_Unknown_type, Just [Typ_error(pos, Tycon_mismatched)])
                                           _ -> ras_assert False (Ras_Unknown_type, Just [Typ_error(pos, Expr_illegal_operation)])
                                        )
    Mediate_code_raw_Var v_body -> (case v_body of
                                      Mediate_var_attr {..} -> (var_type, Nothing)
                                      _ -> ras_assert False (Ras_Unknown_type, Just [Typ_error((-1, -1), Decl_illegal_construct)])
                                   )
    Mediate_code_raw_Una {mnemonic = (pos_m, m)} -> let (ty_expr0, r') = tyinf (operand_0 expr)
                                                    in
                                                      if (m == Mn_neg) then
                                                        (if (is_subtype ty_expr0 Ras_Real) then (ty_expr0, r')
                                                         else (Ras_Bottom_type, Just [Typ_error(pos_m, Tycon_mismatched)])
                                                        )
                                                      else
                                                        if ((m == Mn_preinc) || (m == Mn_pstinc) || (m == Mn_predec) || (m == Mn_pstdec)) then
                                                          (if (ty_expr0 == Ras_Integer) then (Ras_Integer, r')
                                                           else (Ras_Bottom_type, Just [Typ_error(pos_m, Tycon_mismatched)])
                                                          )
                                                        else
                                                          if (m == Mn_nop) then (ty_expr0, r')
                                                          else
                                                            ras_assert False (Ras_Unknown_type, Just [Typ_error(pos_m, Expr_illegal_operation)])
                                                               
    Mediate_code_raw_Bin {mnemonic = (pos_m, m)} -> let (ty_expr0, r_0) = tyinf (operand_0 expr)
                                                        (ty_expr1, r_1) = tyinf (operand_1 expr)
                                                    in
                                                      let r' = append_error r_1 r_0
                                                      in
                                                        if ((m == Mn_add) || (m == Mn_sub) || (m == Mn_mul)) then
                                                          if ((is_subtype ty_expr0 Ras_Real) && (is_subtype ty_expr1 Ras_Real)) then
                                                            (if (is_subtype ty_expr0 ty_expr1) then (ty_expr1, r')
                                                             else (if (is_subtype ty_expr1 ty_expr0) then (ty_expr0, r')
                                                                   else (Ras_Bottom_type, Just [Typ_error(pos_m, Tycon_mismatched)])
                                                                  )
                                                            )
                                                          else (Ras_Bottom_type, Just [Typ_error(pos_m, Tycon_mismatched)])
                                                        else
                                                          if (m == Mn_div) then
                                                            if ((is_subtype ty_expr0 Ras_Real) && (is_subtype ty_expr1 Ras_Real)) then (Ras_Real, r')
                                                            else (Ras_Bottom_type, Just [Typ_error(pos_m, Tycon_mismatched)])
                                                          else
                                                            if (m == Mn_mod) then
                                                              if ((is_subtype ty_expr0 Ras_Real) && (is_subtype ty_expr1 Ras_Real)) then
                                                                (if ((ty_expr0 == Ras_Integer) && (ty_expr1 == Ras_Integer)) then (Ras_Integer, r')
                                                                 else (Ras_Real, r')
                                                                )
                                                              else (Ras_Bottom_type, Just [Typ_error(pos_m, Tycon_mismatched)])
                                                            else
                                                              ras_assert False (Ras_Unknown_type, Just [Typ_error(pos_m, Expr_illegal_operation)])
    Mediate_code_fragment_raw_None _  -> (Ras_Bottom_type, Nothing)
    _ -> ras_assert False (Ras_Unknown_type, Just [Typ_error((-1, -1), Expr_illegal_expression)])
  )


typecheck ((row, col), tk_code) expr = {- Updating types of each sub-expr. in given expr, by type inference. -}
  ras_trace "in typecheck" (
  case expr of
    {- If e1 : T1, e2 : T2, and T2 <: T1, then (e1:T1 := e2:T2) : T1. -}
    Mediate_code_raw_Bin {mnemonic = (pos_m, m)}
      | m == Mn_asgn -> let lvalue = operand_0 expr
                            rvalue = operand_1 expr
                        in
                          case lvalue of
                            Mediate_code_raw_Var var@(Mediate_var_attr {..}) -> let (ty_l, r_l) = tyinf lvalue
                                                                                    (ty_r, r_r) = tyinf rvalue
                                                                                in
                                                                                  let r = append_error r_r r_l
                                                                                  in
                                                                                    if (ty_l == Ras_Bottom_type) then
                                                                                      let lvalue' = Mediate_code_raw_Var var{var_type = ty_r}
                                                                                      in
                                                                                        (expr{operand_0 = lvalue'}, r)
                                                                                    else
                                                                                      if (is_subtype ty_r ty_l) then (expr, r)
                                                                                      else (expr, (add_error r (Par_error (var_coord, Tycon_mismatched))))
                            _ -> ras_assert False (expr, Just [(Par_error ((row, col), Compiler_internal_error))])
      | otherwise -> (expr, Nothing)
    _ -> (expr, Nothing)
  )


data Sym_category =
  Cat_Sym_typedef
  | Cat_Sym_func
  | Cat_Sym_record
  | Cat_Sym_decl
  deriving (Eq, Ord, Show)

data Sym_entity =
  Sym_var Mediate_var_attr
  | Sym_typedef Ras_typedef_attr0
  | Sym_record Ras_Record_attr
    deriving (Eq, Ord, Show)

data Sym_attr_type =
  Attrib_Var Mediate_var_attr
  | Attrib_Rec Ras_Record_attr
  | Attrib_Typedef Ras_typedef_attr0
  deriving (Eq, Ord, Show)

data Sym_attrib =
  Sym_attrib {attr_live :: ((Int, Int), Sym_attr_type), attr_decl :: Mediate_code_fragment_raw}
  deriving (Eq, Ord, Show)

data Symtbl_node =
  Sym_entry {sym_ident :: String, sym_body :: Sym_attrib}
  deriving (Eq, Ord, Show)

data Symtbl_cluster =
  Sym_empty
  | Sym_add Symtbl_node Symtbl_cluster
  deriving (Eq, Ord, Show)

data Symtbl_anon_ident =
  Symtbl_anon_ident {sym_anon_var :: Integer, sym_anon_record :: Integer}
  deriving (Eq, Ord, Show)

data Sym_tbl =
  Scope_empty
  | Scope_add (Int, Symtbl_anon_ident, Symtbl_cluster) Sym_tbl
  deriving (Eq, Ord, Show)

data Symtbl =
  Symtbl {sym_typedef :: Sym_tbl, sym_func :: Sym_tbl, sym_record :: Sym_tbl, sym_decl :: Sym_tbl}
  deriving (Eq, Ord, Show)


sym_categorize symtbl cat =
  ras_trace "in sym_categorize" (
  case cat of
    Cat_Sym_typedef -> sym_typedef symtbl
    Cat_Sym_func -> sym_func symtbl
    Cat_Sym_record -> sym_record symtbl
    Cat_Sym_decl -> sym_decl symtbl
  )


sym_update symtbl cat tbl =
  ras_trace "in sym_update" (
  case cat of
    Cat_Sym_typedef -> symtbl{sym_typedef = tbl}
    Cat_Sym_func -> symtbl{sym_func = tbl}
    Cat_Sym_record -> symtbl{sym_record = tbl}
    Cat_Sym_decl -> symtbl{sym_decl = tbl}
  )


sym_search symtbl cat ident =
  ras_trace "in sym_search" (
  let walk syms ident =
        case syms of
          Sym_empty -> Nothing
          Sym_add sym syms' -> if ((sym_ident sym) == ident) then Just (sym, syms')
                               else walk syms' ident
  in
    let sym_tbl = sym_categorize symtbl cat
    in
      case sym_tbl of
        Scope_empty -> Nothing
        Scope_add (lv, anon_idents, syms) sym_tbl' ->
          (case (walk syms ident) of
             Just (found, syms') -> Just ((sym_body found), sym_update symtbl cat (Scope_add (lv, anon_idents, syms') sym_tbl'))
             Nothing -> sym_search (sym_update symtbl cat sym_tbl') cat ident
          )
  )


sym_lookup_var symtbl cat ident =
  ras_trace "in sym_lookup_var" (
  let trying = sym_search symtbl cat ident
  in
    case trying of
      Nothing -> Nothing
      Just (whole_attr, remainders) -> (case (attr_live whole_attr) of
                                          (pos, (Attrib_Var av)) -> Just (av, attr_decl whole_attr)
                                          _ -> sym_lookup_var remainders cat ident )
  )


sym_lookup_var_decl symtbl ident =
  ras_trace "in sym_lookup_var_decl" (
  sym_lookup_var symtbl Cat_Sym_decl ident
  )


sym_lookup_rec symtbl cat ident =
  ras_trace "in sym_lookup_rec" (
  let trying = sym_search symtbl cat ident
  in
    case trying of
      Nothing -> Nothing
      Just (whole_attr, remainders) -> (case (attr_live whole_attr) of
                                          (pos, (Attrib_Rec ar)) -> Just (ar, attr_decl whole_attr)
                                          _ -> sym_lookup_rec remainders cat ident )
  )


sym_lookup_rec_decl symtbl ident =
  ras_trace "in sym_lookup_rec_decl" (
  sym_lookup_rec symtbl Cat_Sym_decl ident
  )


sym_lookup_typedef symtbl ident =
  ras_trace "in sym_lookup_typedef" (
  let trying = sym_search symtbl Cat_Sym_typedef ident
  in
    case trying of
      Nothing -> Nothing
      Just (whole_attr, remainders) -> (case (attr_live whole_attr) of
                                          (pos, (Attrib_Typedef at)) -> Just (at, attr_decl whole_attr)
                                          _ -> sym_lookup_typedef remainders ident )
  )


sym_lookup_typedef_decl symtbl ident =
  ras_trace "in sym_lookup_typedef_decl" (
  sym_lookup_typedef symtbl ident
  )


walk_on_scope sym_cluster (kind, tgt_id) =
  ras_trace "in walk_on_scope" (
  let cmp_kind (Sym_entry {sym_body = attr}) =
        let attr_type = attr_live attr
        in
          case kind of
            Sym_var _ -> (case attr_type of
                            (pos, (Attrib_Var _)) -> True
                            _ -> False )
            Sym_typedef _ -> (case attr_type of
                                (pos, (Attrib_Typedef _)) -> True
                                _ -> False )
            Sym_record _  -> (case attr_type of
                                (pos, (Attrib_Rec _ ))-> True
                                _ -> False )
  in
    case sym_cluster of
      Sym_empty -> Nothing
      Sym_add sym sym_cluster' -> if ((cmp_kind sym) && ((sym_ident sym) == tgt_id)) then Just sym
                                  else walk_on_scope sym_cluster' (kind, tgt_id)
  )


sym_regist ovwt symtbl cat entity fragment =
  ras_trace "in sym_regist" (
  let reg_sym sym_tbl ident sym =
        case sym_tbl of
          Scope_empty ->
            ((Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, (Sym_add sym Sym_empty)) Scope_empty), Nothing)
          Scope_add (lv, anon_ident_crnt, syms) sym_tbl' ->
            (case syms of
               Sym_empty -> ((Scope_add (lv, anon_ident_crnt, (Sym_add sym Sym_empty)) sym_tbl'), Nothing)
               Sym_add _ _ -> (case (walk_on_scope syms (entity, ident)) of
                                 Just e -> if (not ovwt) then (sym_tbl, Just Symbol_redifinition)
                                           else ((Scope_add (lv, anon_ident_crnt, (Sym_add sym syms)) sym_tbl'), Nothing)
                                 Nothing -> ((Scope_add (lv, anon_ident_crnt, (Sym_add sym syms)) sym_tbl'), Nothing)
                              )
            )
  in
    let sym_tbl' =
          let sym_tbl = sym_categorize symtbl cat
          in
            case entity of
              Sym_var decl@(Mediate_var_attr {var_ident = v_id}) ->
                let pos = (-1, -1)
                in
                  reg_sym sym_tbl v_id (Sym_entry {sym_ident = v_id, sym_body = Sym_attrib {attr_live = (pos, (Attrib_Var decl)), attr_decl = fragment}})
              Sym_typedef tydef_attr@(Ras_typedef_attr0 {..}) ->
                reg_sym sym_tbl tydef_ident (Sym_entry {sym_ident = tydef_ident, sym_body = Sym_attrib {attr_live = (tydef_coord, (Attrib_Typedef tydef_attr)), attr_decl = fragment}})
              Sym_record (pos, rec_id, fields) ->
                reg_sym sym_tbl rec_id (Sym_entry {sym_ident = rec_id, sym_body = Sym_attrib {attr_live = (pos, (Attrib_Rec (pos, rec_id, fields))), attr_decl = fragment}})
    in
      case sym_tbl' of
        (tbl', err) -> ((sym_update symtbl cat tbl'), err)
  )


enter_scope symtbl cat =
  ras_trace "in enter_scope" (
  let sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = case sym_tbl of
                     Scope_empty -> Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, Sym_empty) Scope_empty
                     Scope_add (lv, sym_anon_ident, _) _ -> Scope_add (lv + 1, sym_anon_ident, Sym_empty) sym_tbl
    in
      sym_update symtbl cat sym_tbl'
  )


sym_anonid_var symtbl cat pref suff sep =
  ras_trace "in sym_anonid_var" (
  let d2s_var m = "var_" ++ ((pref ++ sep) ++ (show m) ++ (sep ++ suff))
      sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = (case sym_tbl of
                      Scope_empty -> sym_categorize (enter_scope symtbl cat) cat
                      Scope_add _ _ -> sym_tbl )
    in
      let r = case sym_tbl' of
                Scope_add (lv, anon_crnt@(Symtbl_anon_ident {sym_anon_var = crnt_top}), syms) sym_tbl'' ->
                  ((d2s_var crnt_top), Scope_add (lv, anon_crnt {sym_anon_var = crnt_top + 1}, syms) sym_tbl'')
      in
        case r of
          (anonid, tbl') -> (anonid ++ suff, sym_update symtbl cat tbl')
  )


sym_anonid_rec symtbl cat pref suff sep =
  ras_trace "in sym_anonid_rec" (
  let d2s_rec m = "rec_" ++ ((pref ++ sep) ++ (show m) ++ (sep ++ suff))
      sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = (case sym_tbl of
                      Scope_empty -> sym_categorize (enter_scope symtbl cat) cat
                      Scope_add _ _ -> sym_tbl )
    in
      let r = case sym_tbl' of
                Scope_add (lv, anon_crnt@(Symtbl_anon_ident {sym_anon_record = crnt_top}), syms) sym_tbl'' ->
                  ((d2s_rec crnt_top), Scope_add (lv, anon_crnt {sym_anon_record = crnt_top + 1}, syms) sym_tbl'')
      in
        case r of
          (anonid, tbl') -> (anonid, sym_update symtbl cat tbl')
  )


leave_scope symtbl cat =
  ras_trace "in leave_scope" (
  let sym_tbl = sym_categorize symtbl cat
  in
    let sym_tbl' = case sym_tbl of
                     Scope_empty -> Scope_empty
                     Scope_add sco sym_tbl' -> sym_tbl'
    in
      sym_update symtbl cat sym_tbl'
  )


par_typedef symtbl tokens0@(((row0, col0), tk0):tokens) =
  let par_tydef_body acc symtbl tokens0'@(((row0', col0'), tk0'):tokens') =
        let tydef_attr = Ras_typedef_attr0 {tydef_coord = (row0, col0), tydef_ident = "", tydef_deftype = Ras_Unknown_type}
            fragment = Mediate_code_raw_typedef tydef_attr
            acc' = acc ++ [fragment]
        in
          case tokens' of
            ((row_i, col_i), IDENT t_ident):(ts0'@(((row_a, col_a), ASGN):ts')) ->
              let tydef_attr' = tydef_attr{tydef_coord = (row_i, col_i), tydef_ident = t_ident}
                  fragment' = Mediate_code_raw_typedef tydef_attr'
                  acc' = acc ++ [fragment']
                  tk2ty tk =
                    case tk of
                      (_, BOOLEAN) -> (Just Ras_Boolean, symtbl, ts', Nothing)
                      (_, INTEGER) -> (Just Ras_Integer, symtbl, ts', Nothing)
                      (_, REAL) -> (Just Ras_Real, symtbl, ts', Nothing)
                      (_, STRING) -> (Just Ras_String, symtbl, ts', Nothing)
                      (_, CHAR) -> (Just Ras_Char, symtbl, ts', Nothing)
                      (pos, RECORD) -> let qual = Ras_Record (pos, "", [])
                                       in
                                         (case (par_record symtbl qual ts') of
                                            (r_ident, symtbl', tokens'', Nothing) -> (case (sym_lookup_rec symtbl' Cat_Sym_record r_ident) of
                                                                                        Just (r_attr, _) -> (Just (Ras_Record r_attr), symtbl', tokens'', Nothing)
                                                                                        Nothing -> ras_assert False (Nothing, symtbl', tokens'', Just [Par_error (pos, Compiler_internal_error)]) )
                                            (r_ident, symtbl', tokens'', err) -> (Nothing, symtbl', tokens'', err)
                                         )
                      (pos, IDENT ty_ident) -> (case (sym_lookup_typedef symtbl ty_ident) of
                                                  Just (Ras_typedef_attr0 {tydef_coord = pos', tydef_ident = ty_ident', tydef_deftype = deftype}, _) ->
                                                    (case (ras_assert (ty_ident' == ty_ident) deftype) of
                                                       Ras_Typedef _ -> assert False (Nothing, symtbl, ts', Just [Par_error (pos, Compiler_internal_error)])
                                                       ty | ((ty == Ras_Bottom_type) || (ty == Ras_Unknown_type) || (ty == Ras_Illformed_type)) ->
                                                            (Nothing, symtbl, ts', Just [Par_error (pos, Typedef_invalid_synon_type)])
                                                       _ -> (Just deftype, symtbl, ts', Nothing)
                                                    )
                                                  Nothing -> (Nothing, symtbl, ts', Just [Par_error (pos, Typedef_invalid_synon_type)])
                                               )
                      (pos, _) -> (Nothing, symtbl, ts', Just [Par_error (pos, Typedef_invalid_synon_type)])
              in
                (case ts' of
                   t':_ -> (case (tk2ty t') of
                               (Just ty, symtbl', tokens'', Nothing) ->
                                 let entity = Sym_typedef (Ras_typedef_attr0 {tydef_coord = (row_i, col_i), tydef_ident = t_ident, tydef_deftype = ty})
                                     tydef_attr'' = tydef_attr'{tydef_deftype = ty}
                                     fragment'' = Mediate_code_raw_typedef tydef_attr''
                                     acc' = acc ++ [fragment'']
                                 in
                                   case (sym_regist False symtbl' Cat_Sym_typedef entity fragment'') of
                                     (symtbl'', err) -> (case err of
                                                           Nothing -> (case tokens'' of
                                                                         t0'':ts'' -> (case ts'' of
                                                                                         (_, SEMICOL):(pos'', RBRA):tokens'' -> (acc' ,symtbl'', ((pos'', RBRA):tokens''), Nothing)
                                                                                         (pos'', RBRA):tokens'' -> (acc', symtbl'', ts'', Nothing)
                                                                                         (pos'', SEMICOL):tokens'' -> par_tydef_body acc' symtbl'' ts''
                                                                                         _ -> (acc', symtbl'', tokens'', Just [(Par_error ((row_i, col_i), Typedef_illformed_declarement))]) )
                                                                         _ -> (acc', symtbl'', tokens'', Just [(Par_error ((row_i, col_i), Typedef_illformed_declarement))])
                                                                      )
                                                           Just e -> let e' = Par_error ((row_i, col_i), e)
                                                                     in
                                                                       let es = (case e of
                                                                                   Symbol_redifinition -> (Par_error ((row_i, col_i), Typedef_redefinition))
                                                                                   _ -> ras_assert False (Par_error ((row_i, col_i), Compiler_internal_error))
                                                                                ) : [e']
                                                                       in
                                                                         (acc', symtbl'', tokens'', Just es)
                                                        )
                               (Nothing, symtbl', tokens'', err) -> let tydef_attr'' = tydef_attr'{tydef_deftype = Ras_Illformed_type}
                                                                        fragment'' = Mediate_code_raw_typedef tydef_attr''
                                                                        acc' = acc ++ [fragment'']
                                                                    in
                                                                      case err of
                                                                        Just es -> (acc', symtbl', tokens'', err)
                                                                        Nothing -> ras_assert False (acc', symtbl', tokens'', err)
                           )
                   _ -> (acc', symtbl, ts0', Just [(Par_error ((row_a, col_a), Typedef_no_synon_type))])
                )
            ((row_i, col_i), IDENT t_ident):ts' -> (acc', symtbl, tokens', Just [(Par_error ((row_i, col_i), Typedef_no_synon_type))])
            ((row_i, col_i), _):ts' -> (acc', symtbl, tokens', Just [(Par_error ((row_i, col_i), Typedef_no_synon_name))])
            _ -> (acc', symtbl, tokens', Just [(Par_error ((row0', col0'), Typedef_illformed_declarement))])
  in
    let fragment = Mediate_code_raw_typedef (Ras_typedef_attr0 {tydef_coord = (row0, col0), tydef_ident = "", tydef_deftype = Ras_Unknown_type})
    in
      case (assert (tk0 == TYPE) tokens) of
        (_, LBRA):ts -> (case ts of
                           (_, RBRA):ts' -> ([fragment], symtbl, ts, Nothing)
                           (_, _):ts' -> par_tydef_body [] symtbl tokens
                        )
        _ -> ([fragment], symtbl, tokens0, Just [(Par_error ((row0, col0), Typedef_illformed_declarement))])


par_record symtbl qual@(Ras_Record ((r_decl, c_decl), _, _)) tokens0@(((row0, col0), tk0):tokens) =
  ras_trace "in par_record" (
  let decl_fields acc symtbl tokens0@((pos0, _):tokens) =
        let decl_type symtbl tokens0@((pos0, _):tokens) =
              case tokens of
                (_, BOOLEAN):ts -> (Ras_Boolean, symtbl, tokens, Nothing)
                (_, INTEGER):ts -> (Ras_Integer, symtbl, tokens, Nothing)
                (_, REAL):ts -> (Ras_Real, symtbl, tokens, Nothing)
                (_, STRING):ts -> (Ras_String, symtbl, tokens, Nothing)
                (_, CHAR):ts -> (Ras_Char, symtbl, tokens, Nothing)
                (pos, RECORD):ts ->
                  let qual' = Ras_Record (pos, "", [])
                  in
                    (case (par_record symtbl qual' tokens) of
                       (r_ident, symtbl', tokens', Nothing) -> (case (sym_lookup_rec symtbl' Cat_Sym_record r_ident) of
                                                                  Just (sig, _) -> (Ras_Record sig, symtbl', tokens', Nothing)
                                                                  Nothing -> assert False (Ras_Unknown_type, (leave_scope symtbl' Cat_Sym_record), tokens',
                                                                                           Just [(Par_error (pos, Compiler_internal_error))])
                                                               )
                       (_, symtbl', tokens', err) -> (Ras_Illformed_type, (leave_scope symtbl' Cat_Sym_record), tokens', err)
                    )
                (pos, IDENT ty_ident):ts -> (case (sym_lookup_typedef symtbl ty_ident) of
                                               Just (Ras_typedef_attr0 {tydef_coord = pos', tydef_ident = ty_ident', tydef_deftype = deftype}, _) ->
                                                 (case (ras_assert (ty_ident' == ty_ident) deftype) of
                                                    Ras_Typedef _ -> assert False (Ras_Illformed_type, symtbl, tokens, Just [Par_error (pos, Compiler_internal_error)])
                                                    ty | ((ty == Ras_Bottom_type) || (ty == Ras_Unknown_type) || (ty == Ras_Illformed_type)) ->
                                                         (Ras_Illformed_type, symtbl, tokens, Just [(Par_error (pos, Illformed_Declarement))])
                                                    _ -> (deftype, symtbl, tokens, Nothing)
                                                 )
                                               Nothing -> (Ras_Illformed_type, symtbl, tokens, Just [(Par_error (pos, Illformed_Declarement))])
                                            )
                (pos, _):ts -> (Ras_Illformed_type, symtbl, tokens0, Just [(Par_error (pos, Illformed_Declarement))])
                _ ->(Ras_Illformed_type, symtbl, tokens0, Just [(Par_error (pos0, Illformed_Declarement))])
        in
          case tokens of
            (pos, IDENT f_ident):ts ->
              let field = Ras_Record_field {memb_coord = pos, memb_ident = f_ident, memb_type = Ras_Unknown_type}
              in
                (case ts of
                   (pos', TYPED_AS):ts' -> (case (decl_type symtbl ts) of
                                              (f_type, symtbl', tokens', err) ->
                                                let acc' = acc ++ [field{memb_type = f_type}]
                                                in
                                                  case err of
                                                    Nothing -> (case tokens' of
                                                                  (_, _):(pos'', SEMICOL):ts'' -> decl_fields acc' symtbl' ((pos'', SEMICOL):ts'')
                                                                  (_, _):(pos'', _):ts'' -> (acc', symtbl', tokens', Nothing)
                                                                  (_, _):ts'' -> (acc', symtbl', tokens', Nothing)
                                                                  _ -> (acc', symtbl', tokens', Nothing) )
                                                    _ -> (acc', symtbl', tokens', err)
                                           )
                   (pos', _):ts' -> ((acc ++ [field]), symtbl, tokens, Just [(Par_error (pos', Illformed_Declarement))])
                   _ -> ((acc ++ [field]), symtbl, tokens, Just [(Par_error (pos, Illformed_Declarement))])
                )
            (_, _):ts -> (acc, symtbl, tokens0, Nothing)
            _ -> (acc, symtbl, tokens0, Nothing)
  in
    let (r_ident, symtbl') = sym_anonid_rec symtbl Cat_Sym_record "" "" ""
    in
      case tokens of
        (pos, LBRA):ts -> (case (decl_fields [] (enter_scope symtbl' Cat_Sym_record) tokens) of
                             (fields, symtbl', tokens', Nothing) ->
                               (case tokens' of
                                  (pos0', _):(pos', RBRA):ts' ->
                                    let tokens'' = (pos', RBRA):ts'
                                        r_fragment = Mediate_code_raw_Var (Mediate_var_attr {var_coord = (r_decl, c_decl), var_ident = r_ident,
                                                                                             var_type = Ras_Record ((r_decl, c_decl),r_ident, fields),
                                                                                             var_attr = Var_attr_fields []})
                                    in
                                      (case (sym_regist False (leave_scope symtbl' Cat_Sym_record) Cat_Sym_record (Sym_record ((r_decl, c_decl), r_ident, fields)) r_fragment) of
                                         (symtbl'', Nothing) -> (r_ident , symtbl'', (pos', RBRA):ts', Nothing)
                                         (symtbl'', Just err) -> (r_ident , symtbl'', (pos', RBRA):ts', Just [(Par_error (pos', err))]) )
                                  (pos0', _):(pos', _):ts' -> (r_ident , symtbl', tokens', Just [(Par_error (pos', Illformed_Declarement))])
                                  (pos0', _):ts' -> (r_ident , symtbl', tokens', Just [(Par_error (pos0', Illformed_Declarement))])
                                  _ -> ras_assert False (r_ident , symtbl', tokens', Just [(Par_error (pos, Compiler_internal_error))])
                               )
                             (fields, symtbl', tokens', err) -> (r_ident, symtbl', tokens', err)
                          )
        (pos, _):ts -> (r_ident, symtbl', tokens0, Just [(Par_error (pos, Illformed_Declarement))])
        _ -> (r_ident, symtbl', tokens0, Just [(Par_error ((row0, col0), Illformed_Declarement))])
  )


par_init_on_decl symtbl reg vars tokens0@(((row0, col0), tk0):tokens) =
  ras_trace "in par_init_on_decl" (
  case vars of
    [] -> (symtbl, [], tokens0, Nothing)
    (v@(Mediate_code_raw_Var v_attr)):vs ->
      case (var_type v_attr) of
        ty_r@(Ras_Record (_, r_ident, fields)) ->
          let (symtbl', vars', tokens', err) = (case tokens of
                                                  ((row, col), DEF):ts ->
                                                    (case ts of
                                                       ((row', col'), LBRA):ts' ->
                                                         (case (par_record_const [] symtbl (r_ident, fields) ts) of
                                                            (symtbl', ini_fields, tokens', err) ->
                                                              (case err of
                                                                 Nothing ->
                                                                   let init ini_fields var =
                                                                         case var of
                                                                           Mediate_code_raw_Var v_attr@(Mediate_var_attr {var_type = ty}) ->
                                                                             let v_attr' = (ras_assert (ty == ty_r) v_attr){var_attr = Var_attr_fields ini_fields}
                                                                             in
                                                                               Mediate_code_raw_Var v_attr'
                                                                           _ -> ras_assert False var
                                                                   in
                                                                     (symtbl', (map (init ini_fields) vars), tokens', err)
                                                                 Just _ -> (symtbl', vars, tokens', err) )
                                                         )
                                                       ((row', col'), _):ts' -> (symtbl, vars, tokens, Just [(Par_error ((row', col'), Illformed_Declarement))])
                                                       _ -> (symtbl, vars, tokens, Just [(Par_error ((row, col), Illformed_Declarement))])
                                                    )
                                                  _ -> (symtbl, vars, tokens0, Nothing)
                                               )
          in
            let def_and_reg symtbl (vars, errs) =
                  case vars of
                    [] -> (symtbl, [], errs)
                    (v@(Mediate_code_raw_Var v_attr@(Mediate_var_attr {var_type = ty}))):vs ->
                      let (symtbl', r) = sym_regist False symtbl Cat_Sym_decl (Sym_var v_attr) v
                      in
                        case r of
                          Nothing -> (case (def_and_reg symtbl' (vs, errs)) of
                                        (symtbl', vs', errs') -> (symtbl', v:vs', errs') )
                          Just sym_err -> let errs' = add_error errs (Par_error ((var_coord v_attr), sym_err))
                                          in
                                            case (def_and_reg symtbl' (vs, errs')) of
                                              (symtbl', vs', errs'') -> (symtbl', v:vs', errs'')
                    _ -> ras_assert False (symtbl, vars, errs)
            in
              if reg then (case (def_and_reg symtbl' (vars', err)) of
                             (symtbl'', vars'', err') -> (symtbl'', vars'', tokens', err') )
              else (symtbl', vars', tokens', err)
        
        _ -> let pairing val =
                   case val of
                     Mediate_code_raw_Var v@(Mediate_var_attr {var_attr = v_attr}) ->
                       (case v_attr of
                          Var_attr_const (pos, c) -> let lvalue = val
                                                         rvalue = Mediate_code_raw_Literal (pos, c)
                                                     in
                                                       Mediate_code_raw_Bin {mnemonic = ((row0, col0), Mn_asgn), operand_0 = lvalue, operand_1 = rvalue}
                          _ -> ras_assert False val
                       )
                     _ -> val
                 
                 folding exprs =
                   let strip expr =
                         case expr of
                           Mediate_code_raw_Bin {operand_0 = lvalue} -> lvalue
                           _ -> ras_assert False expr
                   in
                     case exprs of
                       [] -> ([], Nothing)
                       (e, err):es -> (case (folding es) of
                                         (es', _) -> (((strip e):es'), err) )
                 
                 def_and_reg symtbl (vars, errs) =
                   if reg then (case vars of
                                  [] -> (symtbl, [], errs)
                                  (v@(Mediate_code_raw_Var var)):vs ->
                                    let (symtbl', r) = sym_regist True symtbl Cat_Sym_decl (Sym_var var) v
                                    in
                                      case r of
                                        Nothing -> (case (def_and_reg symtbl' (vs, errs)) of
                                                      (symtbl', vars', errs') -> (symtbl', v:vars', errs') )
                                        Just sym_err -> let errs' = add_error errs (Par_error ((var_coord var), sym_err))
                                                        in
                                                          case (def_and_reg symtbl' (vs, errs')) of
                                                            (symtbl', vars', errs'') -> (symtbl', v:vars', errs'')
                                  _ -> ras_assert False (symtbl, vars, errs)
                               )
                   else
                     (symtbl, vars, errs)
             in
               let init (row_c, col_c) c = pairing . (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_attr = Var_attr_const ((row_c, col_c), c)}))
               in
                 case (case tokens of
                         (t@((row, col), (BOOL_CONST b))):ts -> (def_and_reg symtbl (folding (map ((typecheck t) . (init (row, col) (Boolean_const b))) vars)), tokens)
                         (t@((row, col), (CHR_CONST c))):ts -> (def_and_reg symtbl (folding (map ((typecheck t) . (init (row, col) (Char_const c))) vars)), tokens)
                         (t@((row, col), (STR_CONST s))):ts -> (def_and_reg symtbl (folding (map ((typecheck t) . (init (row, col) (String_const s))) vars)), tokens)
                         (t@((row, col), (NUM_CONST n))):ts -> (def_and_reg symtbl (folding (map ((typecheck t) . (init (row, col) (Numeric_const n))) vars)), tokens)
                         (t@((row, col), _)):ts -> ((symtbl, vars, Just [(Par_error ((row, col), Illformed_Declarement))]), tokens0)
                         _ -> ((symtbl, vars, Just [(Par_error ((row0, col0), Illformed_Declarement))]), tokens0) ) of
                   ((symtbl', vars', err), tokens') -> (symtbl', vars', tokens', err)
    _ -> (symtbl, [], tokens0, Nothing)
  )


par_record_const acc symtbl (r_ident, fields) tokens0@(((row0, col0), _):tokens) =
  ras_trace "in par_record_const" (
  case fields of
    [] -> (case tokens of
             (_, RBRA):ts -> (symtbl, acc, ts, Nothing)
             ((row, col), _):ts -> (symtbl, acc, tokens, Just [Par_error ((row, col), Illformed_Declarement)])
             _ -> (symtbl, acc, [], Just [Par_error ((row0, col0), Illformed_Declarement)])
          )
    f:fs ->
      (case (memb_type f) of
         Ras_Record (_, r_nested_ident, r_nested_fields) ->
           (case tokens of
              ((row, col), LBRA):ts ->
                (case (par_record_const [] symtbl (r_nested_ident, r_nested_fields) tokens) of
                   (symtbl', acc_nested, tokens', err) -> let acc' = acc ++ [Mediate_code_raw_Var (Mediate_var_attr {var_coord = (row, col),
                                                                                                                     var_ident = (memb_ident f),
                                                                                                                     var_type = (memb_type f),
                                                                                                                     var_attr = (Var_attr_fields acc_nested)})]
                                                          in
                                                            case err of
                                                              Nothing -> tailing fs (acc', symtbl', tokens')
                                                              Just _ -> (symtbl', acc', tokens', err)
                )
              ((row, col), _):ts -> (symtbl, acc, tokens, Just [Par_error ((row, col), Illformed_Declarement)])
              _ -> (symtbl, acc, [], Just [Par_error ((row0, col0), Illformed_Declarement)])
           )
         _ -> let v_memb = Mediate_code_raw_Var (Mediate_var_attr {var_coord = (memb_coord f), var_ident = (memb_ident f), var_type = (memb_type f),
                                                                   var_attr = (Var_attr_const ((-1, -1), Ras_Const_not_defined))})
              in
                case (par_init_on_decl symtbl False [v_memb] tokens0) of
                  (symtbl', f', tokens', err) -> let acc' = acc ++ f'
                                                 in
                                                   (case err of
                                                      Nothing -> tailing fs (acc', symtbl', tokens')
                                                      Just _ -> (symtbl', acc', tokens', err) )
      )
      
      where tailing fields (acc, symtbl, tokens0@(((row0, col0), _):tokens)) =
              let padding (row_t, col_t) omits =
                    case omits of
                      [] -> []
                      f:fs -> (case (memb_type f) of
                                 Ras_Record (_, r_ident, r_fields) ->
                                   Mediate_code_raw_Var (Mediate_var_attr {var_coord = (row_t, col_t), var_ident = (memb_ident f), var_type = (memb_type f),
                                                                           var_attr = Var_attr_fields (padding (row_t, col_t) r_fields)})
                                 _ -> Mediate_code_raw_Var (Mediate_var_attr {var_coord = (row_t, col_t), var_ident = (memb_ident f), var_type = (memb_type f),
                                                                              var_attr = Var_attr_const ((-1, -1), Ras_Const_not_defined)})
                              ) : (padding (row_t, col_t) fs)
              in
                case fields of
                  [] -> (case tokens of
                           (_, SEMICOL):((row, col), RBRA):ts -> (symtbl, acc, ((row, col), RBRA):ts, Nothing)
                           (_, RBRA):ts -> (symtbl, acc, tokens, Nothing)
                           ((row, col), _):ts -> (symtbl, acc, tokens, Just [Par_error ((row, col), Illformed_Declarement)])
                           _ -> (symtbl, acc, tokens0, Just [Par_error ((row0, col0), Illformed_Declarement)])
                        )
                  _ -> (case tokens of
                          (_, SEMICOL):((row, col), RBRA):ts -> (symtbl, (acc ++ (padding (row, col) fields)), ((row, col), RBRA):ts, Nothing)
                          ((row, col), RBRA):ts -> (symtbl, (acc ++ (padding (row, col) fields)), tokens, Nothing)
                          (_, SEMICOL):ts -> par_record_const acc symtbl (r_ident, fields) tokens
                          ((row, col), _):ts -> (symtbl, (acc ++ (padding (-1, -1) fields)), tokens, Just [Par_error ((row, col), Illformed_Declarement)])
                          _ -> (symtbl, (acc ++ (padding (-1, -1) fields)), tokens0, Just [Par_error ((row0, col0), Illformed_Declarement)])
                       )
  )


par_var acc symtbl tokens0@(((row0, col0), tk0):tokens) =
  ras_trace "in par_var" (
  let tychk_and_reg symtbl var_ty vars tokens0@(((row0, col0), _):tokens) =
        let def_and_reg symtbl vars =
              case vars of
                [] -> (symtbl, [])
                (v@(Mediate_code_raw_Var var)):vs ->
                  let (symtbl', r) = sym_regist False symtbl Cat_Sym_decl (Sym_var var) v
                  in
                    (case r of
                       Nothing -> (case (def_and_reg symtbl' vs) of
                                     (symtbl', vs') -> (symtbl', v:vs') )
                       Just err -> def_and_reg symtbl' vs
                    )
        in
            case tokens of
              ((row, col), DEF):ts -> (case (par_init_on_decl symtbl True vars tokens) of
                                         (symtbl', vars', tokens', err) -> (vars', symtbl', tokens', err) )
              _ -> (case (def_and_reg symtbl vars) of
                      (symtbl', vars') -> (vars', symtbl', tokens0, Nothing) )
  in
    case tokens of
      [] -> (acc, symtbl, tokens0, Just [(Par_error ((row0, col0), Illformed_Declarement))])
      t:ts -> (case t of
                 ((row, col), IDENT v_ident) ->
                   let vars = acc ++ [Mediate_code_raw_Var (Mediate_var_attr {var_coord = (row, col), var_ident = v_ident,
                                                                              var_type = Ras_Bottom_type,
                                                                              var_attr = Var_attr_const ((-1, -1), Ras_Const_not_defined)})]
                   in
                     case ts of
                       t':ts' -> (case t' of
                                    ((row', col'), COMMA) -> par_var vars symtbl ts
                                    ((row', col'), TYPED_AS) ->
                                      (case ts' of
                                         u:us -> let reveal_scl ty vars = map (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_type = ty})) vars
                                                     reveal_rec symtbl r_ident vars =
                                                       let r_attr = case (sym_lookup_rec symtbl Cat_Sym_record r_ident) of
                                                                      Just (sig, _) -> sig
                                                                      _ -> ((-1, -1), r_ident, [])
                                                       in                                                        
                                                         map (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_type = Ras_Record r_attr})) vars
                                                     
                                                 in
                                                   (case u of
                                                      (_, BOOLEAN)-> tychk_and_reg symtbl Ras_Boolean (reveal_scl Ras_Boolean vars) ts'
                                                      (_, INTEGER) -> tychk_and_reg symtbl Ras_Integer (reveal_scl Ras_Integer vars) ts'
                                                      (_, REAL) -> tychk_and_reg symtbl Ras_Real (reveal_scl Ras_Real vars) ts'
                                                      (_, STRING) -> tychk_and_reg symtbl Ras_String (reveal_scl Ras_String vars) ts'
                                                      (_, CHAR) -> tychk_and_reg symtbl Ras_Char (reveal_scl Ras_Char vars) ts'
                                                      ((row'', col''), RECORD) ->
                                                        let qual = Ras_Record ((row'', col''), "", [])
                                                        in
                                                          (case (par_record symtbl qual ts') of
                                                             (r_ident, symtbl', us', err) ->
                                                               (case err of
                                                                  Nothing ->
                                                                    (case (sym_lookup_rec symtbl' Cat_Sym_record r_ident) of
                                                                       Just (r_fields, r_attr) ->
                                                                         (case (par_init_on_decl symtbl' True (reveal_rec symtbl' r_ident vars) us') of
                                                                             (symtbl'', vars', tokens', err') -> (vars', symtbl'', tokens', err') )
                                                                       Nothing ->
                                                                         ras_assert False ((reveal_rec symtbl' r_ident vars), symtbl', us', Just [(Par_error ((row'', col''), Compiler_internal_error))])
                                                                    )
                                                                  _ -> ((reveal_rec symtbl' r_ident vars), symtbl', us', err)
                                                               )
                                                          )
                                                      ((row'', col''), IDENT ty_ident) -> (case (sym_lookup_typedef symtbl ty_ident) of
                                                                                             Just (Ras_typedef_attr0 {tydef_coord = pos, tydef_ident = ty_ident', tydef_deftype = deftype}, _) ->
                                                                                               (case (ras_assert (ty_ident' == ty_ident) deftype) of
                                                                                                  Ras_Typedef (Ras_typedef_attr0 {..}) ->
                                                                                                    ras_assert False (vars, symtbl, ts', Just [(Par_error (tydef_coord, Compiler_internal_error))])
                                                                                                  Ras_Record (pos, r_ident, r_fields) ->
                                                                                                    (case (par_init_on_decl symtbl True (reveal_rec symtbl r_ident vars) ts') of
                                                                                                       (symtbl', vars', tokens', err) -> (vars', symtbl', tokens', err) )
                                                                                                  _ -> tychk_and_reg symtbl deftype (reveal_scl deftype vars) ts'
                                                                                               )
                                                                                             Nothing -> (vars, symtbl, ts', Just [(Par_error ((row'', col''), Illformed_Declarement))])
                                                                                          )
                                                      ((row'', col''), _) -> (acc, symtbl, ts, Just [(Par_error ((row'', col''), Illformed_Declarement))])
                                                   )
                                         _ -> (vars, symtbl, ts, Just [(Par_error ((row', col'), Illformed_Declarement))])
                                      )
                                    _ -> tychk_and_reg symtbl Ras_Bottom_type vars tokens
                                 )
                       _ -> tychk_and_reg symtbl Ras_Bottom_type vars tokens
                 ((row, col), _) -> (acc, symtbl, tokens, Just [(Par_error ((row, col), Illformed_Declarement))])
              )
  )


--par_expr symtbl tokens = (Mediate_code_fragment_raw_None, symtbl, tokens, Nothing)
{-
  numeric_expr := numeric_const | numeric_var
  binary_expr := numeric_expr1 + numeric_expr2 | numeric_expr1 - numeric_expr2 | numeric_expr1 * numeric_expr2 | numeric_expr1 / numeric_expr2 | numeric_expr1 % numeric_expr2
               | binary_expr1 + binary_expr2 | binary_expr1 - binary_expr2 | binary_expr1 * binary_expr2 | binary_expr1 / binary_expr2 | binary_expr1 % binary_expr2 
               | ( binary_expr )
-}
par_expr pre_ope symtbl tokens =
  let tk2ope_una token = (case token of
                            (_, DECL) -> Mn_predec
                            (_, MINUS) -> Mn_neg
                            (_, INCL) ->  Mn_preinc
                            (_, CROSS) -> Mn_nop
                            _ -> ras_assert False Mn_unknown
                         )
      tk2ope_bin token = (case token of
                            (_, CROSS) -> Just Mn_add
                            (_, MINUS) -> Just Mn_sub
                            (_, STAR) -> Just Mn_mul
                            (_, SLASH) -> Just Mn_div
                            (_, PERCENT) -> Just Mn_mod
                            _ -> Nothing
                         )
      par_bin_expr expr1 symtbl tokens ((pos, tk_code), operator) =
        let assoc_l expr2=
              case expr2 of
                Mediate_code_raw_Var _ -> (Mediate_code_raw_Bin {mnemonic = (pos, operator), operand_0 = expr1, operand_1 = expr2}, Nothing)
                Mediate_code_raw_Literal _ -> (Mediate_code_raw_Bin {mnemonic = (pos, operator), operand_0 = expr1, operand_1 = expr2}, Nothing)
                Mediate_code_raw_Par {..} -> (Mediate_code_raw_Bin {mnemonic = (pos, operator), operand_0 = expr1, operand_1 = expr2}, Nothing)
                Mediate_code_raw_Una {..} -> (Mediate_code_raw_Bin {mnemonic = (pos, operator), operand_0 = expr1, operand_1 = expr2}, Nothing)
                Mediate_code_raw_Bin {mnemonic = (pos_m, m), operand_0 = expr2_0, operand_1 = expr2_1}
                  | ((m == Mn_add) || (m == Mn_sub)) -> let (expr2_0', r) = (assoc_l expr2_0)
                                                        in
                                                          (Mediate_code_raw_Bin {mnemonic = (pos_m, m), operand_0 = expr2_0', operand_1 = expr2_1}, r)
                  | ((m == Mn_mul) || (m == Mn_div)) -> if ((operator == Mn_add) || (operator == Mn_sub) || (operator == Mn_mod)) then
                                                          (Mediate_code_raw_Bin {mnemonic = (pos, operator), operand_0 = expr1, operand_1 = expr2}, Nothing)
                                                        else
                                                          if ((operator == Mn_mul) || (operator == Mn_div)) then
                                                            let (expr2_0', r) = (assoc_l expr2_0)
                                                            in
                                                              (Mediate_code_raw_Bin {mnemonic = (pos_m, m), operand_0 = expr2_0', operand_1 = expr2_1}, r)
                                                          else
                                                            ras_assert False ((Mediate_code_fragment_raw_None (pos, tk_code)), Just (Par_error ((-1, -1), Compiler_internal_error)))
                  | (m == Mn_mod) -> (Mediate_code_raw_Bin {mnemonic = (pos_m, m), operand_0 = expr1, operand_1 = expr2}, Nothing)
                  | otherwise -> ras_assert False ((Mediate_code_fragment_raw_None (pos, tk_code)), Just (Par_error ((-1, -1), Compiler_internal_error)))
                Mediate_code_fragment_raw_None (pos', _) ->
                  (Mediate_code_raw_Bin {mnemonic = (pos, operator), operand_0 = expr1, operand_1 = expr2}, Just (Par_error (pos', Expr_illformed_subexpr)))
        in
          let (expr2, symtbl', tokens', r) = (par_expr Nothing symtbl tokens)
          in
            case (assoc_l expr2) of
              (expr', r') -> let r'' = case r' of
                                         Nothing -> r
                                         Just err -> add_error r err
                             in
                               (expr', symtbl', tokens', r'')
  in
    let par_goes_on_num (expr, symtbl, tokens, r) =
          let goes_on = case tokens of
                          [] -> (expr, symtbl, [], r)
                          t:ts -> (case (tk2ope_bin t) of
                                     Just ope -> par_bin_expr expr symtbl ts (t, ope)
                                     Nothing -> (expr, symtbl, tokens, r)
                                  )
          in
            case pre_ope of
              Just _ -> (expr, symtbl, tokens, r)
              Nothing -> goes_on
        par_goes_on_str (expr, symtbl, tokens, r) =
          let goes_on  = case tokens of
                           [] -> (expr, symtbl, [], r)
                           t:ts -> (case (tk2ope_bin t) of
                                      Just ope
                                        | ope == Mn_add -> par_bin_expr expr symtbl ts (t, ope)
                                        | otherwise -> (expr, symtbl, tokens, r)
                                      Nothing -> (expr, symtbl, tokens, r)
                                   )
          in
            case pre_ope of
              Just ((row, col), _) -> (expr, symtbl, tokens, (add_error r (Par_error ((row, col), Expr_illformed_subexpr))))
              Nothing -> goes_on
    in
      let par_una_expr symtbl tokens ((pos, tk_code), operator) =
            let (expr, symtbl', tokens', r) = (par_expr (Just (pos, tk_code)) symtbl tokens)
            in
              case pre_ope of
                Just (pre_pos, _) -> (expr, symtbl', tokens', (add_error r (Par_error (pre_pos, Expr_illegal_operation))))
                Nothing -> (case r of
                              Just err -> (expr, symtbl', tokens', (add_error r (Par_error (pos, Expr_illformed_subexpr))))
                              Nothing -> (case expr of
                                            Mediate_code_fragment_raw_None _ -> (expr, symtbl', tokens', Just [(Par_error (pos, Expr_illformed_subexpr))])
                                            _ -> par_goes_on_num (Mediate_code_raw_Una {mnemonic = (pos, operator), operand_0 = expr}, symtbl', tokens', Nothing)
                                         )
                           )
      in
        case tokens of
          [] -> ((Mediate_code_fragment_raw_None ((-1, -1), EOT)), symtbl, [], Nothing)
          t:ts ->
            (case t of
               ((row, col), INCL) -> par_una_expr symtbl ts (t, (tk2ope_una t))
               ((row, col), CROSS) -> par_una_expr symtbl ts (t, (tk2ope_una t))
               ((row, col), DECL) -> par_una_expr symtbl ts (t, (tk2ope_una t))
               ((row, col), MINUS) -> par_una_expr symtbl ts (t, (tk2ope_una t))
               ((row, col), IDENT var_id) -> (case (sym_lookup_var symtbl Cat_Sym_decl var_id) of
                                                Just (attr, _) -> par_goes_on_num ((Mediate_code_raw_Var attr), symtbl, ts, Nothing)
                                                Nothing -> ((Mediate_code_fragment_raw_None t), symtbl, tokens, Just [(Par_error ((row, col), Symbol_notdefined))])
                                             )
               ((row,col), NUM_CONST n) ->
                 let (expr, tokens', r) = (case n of
                                             Ras_Integer_const _ -> ((Mediate_code_raw_Literal ((row, col), (Numeric_const n))), ts, Nothing)
                                             Ras_Real_const _ -> ((Mediate_code_raw_Literal ((row, col), (Numeric_const n))), ts, Nothing)
                                             _ -> ras_assert False ((Mediate_code_raw_Literal ((row, col), Ras_Const_not_defined)), tokens,
                                                                    Just [(Par_error ((row, col), Compiler_internal_error))])
                                          )
                 in
                   par_goes_on_num (expr, symtbl, tokens', r)
               ((row,col), STR_CONST s) ->
                 let (expr, tokens', r) = (case s of
                                             Ras_String_const _ -> ((Mediate_code_raw_Literal ((row, col), (String_const s))), ts, Nothing)
                                             _ -> ras_assert False ((Mediate_code_raw_Literal ((row, col), Ras_Const_not_defined)), tokens,
                                                                    Just [(Par_error ((row, col), Compiler_internal_error))])
                                          )
                 in
                   par_goes_on_str (expr, symtbl, tokens', r)
               ((row,col), CHR_CONST c) ->
                 let (expr, tokens', r) = (case c of
                                             Ras_Char_const _ -> ((Mediate_code_raw_Literal ((row, col), (Char_const c))), ts, Nothing)
                                             _ -> ras_assert False ((Mediate_code_raw_Literal ((row, col), Ras_Const_not_defined)), tokens,
                                                                    Just [(Par_error ((row, col), Compiler_internal_error))])
                                          )
                 in
                   par_goes_on_str (expr, symtbl, tokens', r)
               ((row, col), LPAR) -> let (expr, symtbl', tokens', r) = (par_expr Nothing symtbl ts)
                                     in
                                       case r of
                                         Just err -> (expr, symtbl', tokens', (add_error r (Par_error ((row, col), Expr_illformed_subexpr))))
                                         Nothing -> (case expr of
                                                       Mediate_code_fragment_raw_None _  -> (expr, symtbl', tokens', Just [(Par_error ((row, col), Expr_illformed_subexpr))])
                                                       _ -> (case tokens' of
                                                               [] -> (expr, symtbl', [], Just [(Par_error ((row, col), Expr_parentheses_mismatched))])
                                                               ((row', col'), RPAR):ts' -> par_goes_on_num (Mediate_code_raw_Par {mnemonic = ((row, col), Mn_prec), operand_0 = expr},
                                                                                                            symtbl', ts', Nothing)
                                                               _ -> (expr, symtbl', tokens', Just [(Par_error ((row, col), Expr_parentheses_mismatched))])
                                                            )
                                                    )
               _ -> ((Mediate_code_fragment_raw_None t), symtbl, tokens, Nothing)
            )


par_asgn symtbl (((row_ident, col_ident), ident), ((row_asgn, col_asgn), tk_asgn)) tokens =
  ras_trace "in par_asgn" (
  case (ras_assert (tk_asgn == ASGN) (sym_lookup_var symtbl Cat_Sym_decl ident)) of
    Just (attr, _) ->
      let fr_asgn = Mediate_code_raw_Bin {mnemonic = ((row_asgn, col_asgn), Mn_asgn), operand_0 = (Mediate_code_raw_Var attr),
                                          operand_1 = (Mediate_code_fragment_raw_None ((-1, -1), EOT))}
          pos_ident = var_coord attr
      in
        case tokens of
          [] -> ([fr_asgn], symtbl, [], Just [(Par_error (pos_ident, Expr_no_valid_rvalue))])
          _ -> (let update symtbl expr_asgn@(Mediate_code_raw_Bin {operand_0 = lvalue}) =
                      case lvalue of
                        Mediate_code_raw_Var var -> let (symtbl', r) = sym_regist True symtbl Cat_Sym_decl (Sym_var var) lvalue
                                                    in
                                                      case r of
                                                        Nothing -> (expr_asgn, symtbl', Nothing)
                                                        Just err -> assert False (expr_asgn, symtbl', Just [(Par_error ((row_ident, col_ident), Compiler_internal_error))])
                        _ -> (expr_asgn, symtbl, Just [(Par_error ((row_asgn, col_asgn), Expr_no_valid_lvalue))])
                in
                  case (par_expr Nothing symtbl tokens) of
                    (expr_r, symtbl', tokens', r) -> let fr_asgn' = fr_asgn{operand_1 = expr_r}
                                                     in
                                                       case (typecheck ((row_ident, col_ident), IDENT ident) fr_asgn') of
                                                         (fr_asgn', Nothing) -> (case (update symtbl fr_asgn') of
                                                                                   (fr_asgn'', symtbl'', r'') -> ([fr_asgn''], symtbl'', tokens', (append_error r r''))
                                                                                )
                                                         (fr_asgn', r') -> ([fr_asgn'], symtbl', tokens', (append_error r r'))
               )
    Nothing ->
      let fr_asgn = Mediate_code_raw_Bin {mnemonic = ((row_asgn, col_asgn), Mn_asgn), operand_0 = (Mediate_code_fragment_raw_None ((row_ident, col_ident), (IDENT ident))),
                                          operand_1 = (Mediate_code_fragment_raw_None ((-1, -1), EOT))}
          err_lhs_notdefined errors =
            let err = Par_error ((row_ident, col_ident), Symbol_notdefined)
            in
              case errors of
                Nothing -> Just [err]
                Just es -> Just (err:es)
      in
        case tokens of
          [] -> ([fr_asgn], symtbl, [], (err_lhs_notdefined (Just [(Par_error ((row_asgn, col_asgn), Expr_no_valid_rvalue))])))
          _ -> (case (par_expr Nothing symtbl tokens) of
                  (expr_r, symtbl', tokens', r) -> ([fr_asgn{operand_1 = expr_r}], symtbl', tokens', (err_lhs_notdefined r))
               )
  )


ras_parse forest symtbl tokens error =
  ras_trace "in ras_parse" (
  let panicked ts =
        case ts of
          [] -> []
          (_, tk_code):ts -> if (tk_code == SEMICOL) then ts else (panicked ts)
  in
    case tokens of
      [] -> (forest, symtbl, [], error)
      t:ts -> (case t of
                 ((row, col), TYPE) -> go_on (par_typedef symtbl tokens)
                 ((row, col), VAR) -> go_on (par_var [] symtbl tokens)
                 ((row, col), IDENT v_ident) -> (case ts of
                                                   [] -> (let (expr, symtbl', tokens', r) = (par_expr Nothing symtbl [t])
                                                          in
                                                            ((forest ++ [expr]), symtbl', tokens', (add_error (append_error error r) (Par_error ((row, col), Expr_has_no_effect))))
                                                         )
                                                   (t'@((row', col'), ASGN)):ts' -> go_on (par_asgn symtbl (((row, col), v_ident), t') ts')
                                                )
                 -- ((row, col), RECORD) ->
                 _ -> ras_parse forest symtbl (panicked tokens) error
              )
        where
          go_on (fragments, symtbl', tokens', err) =
            let forest' = forest ++ fragments
            in
              case err of
                Nothing -> (case tokens' of
                              (_, tk'):ts' -> let tokens'' = if (tk' == SEMICOL) then ts' else (panicked tokens')
                                              in
                                                ras_parse forest' symtbl' tokens'' error
                              _ -> (forest', symtbl', [], error)
                           )
                Just _ -> ras_parse forest' symtbl' (panicked tokens') (append_error error err)
  )


ras_emit_var_decl local_decls forest symtbl =
  let wat_type var_type =
        case var_type of
          Ras_Top_type -> "wat_invalid"
          Ras_Boolean -> "wat_invalid"
          Ras_Integer -> "i64"
          Ras_Real -> "f64"
          Ras_String -> "wat_invalid"
          Ras_Char -> "wat_invalid"
          Ras_Record _ -> "wat_invalid"
          Ras_Typedef _ -> "wat_invalid"
          Ras_Bottom_type -> "wat_invalid"
          Ras_Unknown_type -> "wat_invalid"
          Ras_Illformed_type -> "wat_invalid"
          _ -> "wat_invalid"
  in
    case forest of
      [] -> (local_decls, [])
      t:ts -> let (lvar_decl, (v_id, v_attr)) = (case t of
                                                   Mediate_code_raw_Var Mediate_var_attr {var_ident = v_id, var_type = v_ty, var_attr = v_attr} ->
                                                     (("(local " ++ ("$" ++ v_id) ++ " " ++ (wat_type v_ty) ++ ")"), (v_id, v_attr))
                                                   _ -> ("", (v_id, v_attr))
                                                )
              in
                let (local_decls', local_inits') = ras_emit_var_decl ((if (local_decls == []) then [] else (local_decls ++ [" "])) ++ [lvar_decl]) ts symtbl
                in
                  case v_attr of
                    Var_attr_const (_, (Numeric_const (Ras_Integer_const n))) -> let lvar_init = ("(i64.const " ++ (show n) ++ ")") ++ ("(local.set " ++ ("$" ++ v_id) ++ ")")
                                                                                 in
                                                                                   let local_inits'' = [lvar_init] ++ (if (local_inits' == []) then [] else ([" "] ++ local_inits'))
                                                                                   in
                                                                                     (local_decls', local_inits'')
                    _ -> (local_decls', local_inits')


main src =
  do
    tokens <- return (case (lex src) of
                        [] -> []
                        ts -> if ( (length ts) > (length (lex_purge ts)) ) then [] else ts
                     )
    tokens' <- return (par_real_const ((-1, -1), PHONY) tokens)
    return (let symtbl = Symtbl {sym_typedef = Scope_empty, sym_func = Scope_empty, sym_record = Scope_empty, sym_decl = Scope_empty}
             in
              (tokens', ras_parse [] symtbl tokens' Nothing)
              {- case (ras_parse [] symtbl tokens' Nothing) of
                (forest, symtbl, _, Nothing) -> let (local_decls, local_inits) = ras_emit_var_decl [] forest symtbl
                                                in
                                                  let func_decl = "(func " ++ (concat local_decls) ++ " "
                                                  in
                                                    let local_vars_init = (concat local_inits)
                                                    in
                                                      "(module " ++ (func_decl ++ local_vars_init ++ ")") ++ ")"
                _ -> "" -}
           )
      where
        lex_purge tokens = case tokens of
                             [] -> []
                             (_, SKIPPED _):ts -> lex_purge ts
                             (t:ts) -> t:(lex_purge ts)


-- main "var a :: record { alpha :: integer; beta :: string }"
-- main "var a :: record { alpha :: integer; beta :: string } := { 3; "hello" }"
-- main "var a :: record { alpha :: integer; beta :: record { r1 :: integer } }"
-- main "var a :: record { alpha :: integer; beta :: record { r1 :: integer; r2 :: string } }"
-- main "var a :: integer := 2"
-- main "type { BOOL = integer; STRING = string }"
-- main "type { RECORD = record {i: integer} }"
-- main "type { BOOL = integer; STRING = string }; var a :: BOOL"
-- main "type { BOOL = integer; STRING = string }; var a :: BOOL := 1"
-- main "type { BOOL = integer; STRING = string }; type { BOOL_PRIME = BOOL; BOOL_PRIPRI = BOOL_PRIME }; var a :: BOOL_PRIPRI := 13"
-- main "type {BOOL = integer; PROPERTY = record { PRIVILEGE :: BOOL }}; var a :: PROPERTY := { 1 }"
