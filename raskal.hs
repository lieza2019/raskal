-- :set -XRecordWildCards
{-# LANGUAGE RecordWildCards #-}

import Control.Exception
import Data.Char


data Ras_Error =
  Illformed_Declarement
  | Tycon_mismatched
  | Symbol_redifinition
  | Expr_no_asgn
  | Expr_no_valid_lvalue
  | Expr_no_valid_rvalue
  | Compiler_internal_error
  deriving (Eq, Ord, Show)

data Ras_compiling_err =
  Par_error ((Int, Int), Ras_Error)
  deriving (Eq, Ord, Show)


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


data Ras_Record_field =
  Ras_Record_field {memb_ident :: String, memb_type :: Ras_Types}
  deriving (Eq, Ord, Show)

data Ras_Types =
  Ras_Top_type
  | Ras_Boolean
  | Ras_Integer
  | Ras_Real
  | Ras_String
  | Ras_Char
  | Ras_Record (String, [Ras_Record_field])
  | Ras_Typedef String
  | Ras_Bottom_type
  | Ras_Unknown_type
  | Ras_Illformed_type
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
  Char_const Char_const
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
  | FILE | FOR | FUNCTION
  | GOTO
  | IF | IN | INTEGER
  | LABEL
  | MOD
  | NIL | NOT
  | OF | OR
  | PACKED | PROCEDURE | PROGRAM
  | REAL | RECORD | REPEAT
  | SET
  | THEN | TO | TYPE
  | UNTIL
  | VAR
  | WHILE | WITH
  | COMMA
  | COLON
  | DOT
  | EQU
  | CROSS
  | MINUS
  | STAR | STRING
  | LBRA
  | RBRA
  | LPAR
  | RPAR
  | SEMICOL
  | ASGN
  | TYPED_AS
  | DEF
  | IDENT String
  | NUM_CONST Numeric_const
  | CHR_CONST Char_const
  | STR_CONST String_const
  | SKIPPED String
  | PHONY
  deriving (Eq, Ord, Show)


lex_main lexicon (row, col) src =
  let coding tk_buf cand (row, col) src =
        let elim c cand' =
              case cand' of
                [] -> []
                ((substr, tk_code):cs) -> (case substr of
                                             [] -> []
                                             (c':cs') -> if c' == c then [(cs', tk_code)] else []) ++ (elim c cs)
        in
          let delimiter c = (c /= '_') && not (isAlphaNum c)
          in
            case src of
              [] -> (tk_buf, lookup "" cand, (row, col), [])
              (c:cs) | delimiter c -> (tk_buf, lookup "" cand, (row, col + 1), src)
                     | otherwise -> coding (tk_buf ++ [c]) (elim c cand) (row, col + 1) cs
  in
    case src of
      [] -> []
      (c:cs) | c == '\n' -> lex_main lexicon (row + 1, 0) cs
             | c == '{' -> ((row, col), LBRA):(lex_main lexicon (row, col + 1) cs)
             | c == '}' -> ((row, col), RBRA):(lex_main lexicon (row, col + 1) cs)
             | (c == ' ' || c == '\t') -> lex_main lexicon (row, col + 1) cs
             | c == '=' -> (case cs of
                              '=':cs' -> ((row, col), EQU):(lex_main lexicon (row, col + 2) cs')
                              _ -> ((row, col), ASGN):(lex_main lexicon (row, col + 1) cs) )
             | c == ':' -> (case cs of
                              ':':cs' -> ((row, col), TYPED_AS):(lex_main lexicon (row, col + 2) cs')
                              '=':cs' -> ((row, col), DEF):(lex_main lexicon (row, col + 2) cs')
                              _ -> ((row, col), COLON):(lex_main lexicon (row, col + 1) cs) )
             | c == ';' -> ((row, col), SEMICOL):(lex_main lexicon (row, col + 1) cs)
             | c == ',' -> ((row, col), COMMA):(lex_main lexicon (row, col + 1) cs)
             | c == '.' -> ((row, col), DOT):(lex_main lexicon (row, col + 1) cs)
             | c == '+' -> ((row, col), CROSS):(lex_main lexicon (row, col + 1) cs)
             | c == '-' -> ((row, col), MINUS):(lex_main lexicon (row, col + 1) cs)
             | c == '\'' -> lex_const par_chr_const (row, col + 1) cs
             | c == '"' -> lex_const par_str_const (row, col + 1) cs
             | (isDigit c) -> lex_const ( par_num_const ((ord c) - (ord '0')) ) (row, col + 1) cs
             | otherwise -> (case (coding "" lexicon (row, col) src) of
                               (tk_str, res, (row', col'), rem) -> (case res of
                                                                      Just tk_code -> [((row, col), tk_code)]
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

          par_num_const acc (row, col) src = case src of
                                               [] -> (NUM_CONST (Ras_Integer_const acc), (row, col), [])
                                               (c':cs') | (isDigit c') -> (par_num_const ((acc * 10) + ((ord c') - (ord '0'))) (row, col + 1) cs')
                                                        | otherwise -> (NUM_CONST (Ras_Integer_const acc), (row, col), src)
                                                                     

par_real_const tk_past tokens =
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


data Mediate_code_mnemonic =
  Mn_asgn
  deriving (Eq, Ord, Show)

{- data Mediate_var_attr =
  Mediate_var_attr {var_ident :: String, var_type :: Ras_Types, var_const :: Ras_Const}
  | Mediate_rec_attr {var_ident :: String, var_type :: Ras_Types, var_fields :: [Mediate_code_fragment_raw]}
--  | Mediate_def_attr {var_ident :: String, var_type :: Ras_Types, var_body :: Mediate_code_fragment_raw}
  | Mediate_def_attr {var_ident :: String, var_type :: Ras_Types}
  deriving (Eq, Ord, Show) -}

data Mediate_var_attr =
  Mediate_var_attr {var_coord :: (Int, Int), var_ident :: String, var_type :: Ras_Types, var_attr :: Mediate_var_attr}
  | Var_attr_const Ras_Const
  | Var_attr_fields [Mediate_code_fragment_raw]
  | Var_attr_typedef Mediate_code_fragment_raw
  deriving (Eq, Ord, Show)

data Mediate_code_fragment_raw =
  Mediate_code_fragment_raw_None
  | Mediate_code_raw_Bin {mnemonic :: Mediate_code_mnemonic, operand_0 :: Mediate_code_fragment_raw, operand_1 :: Mediate_code_fragment_raw}
  | Mediate_code_raw_Var Mediate_var_attr
  | Mediate_code_raw_Literal Ras_Const
  deriving (Eq, Ord, Show)


is_subtype ty1 ty2 = {- returns True if ty1 <: ty2, otherwise False. -}
  case ty2 of
    Ras_Top_type -> True
    Ras_Integer -> (ty1 == Ras_Integer) || (ty1 == Ras_Bottom_type)
    Ras_Real -> (ty1 == Ras_Integer) || (ty1 == Ras_Real) || (ty1 == Ras_Bottom_type)
    Ras_String -> (ty1 == Ras_Char) || (ty1 == Ras_String) || (ty1 == Ras_Bottom_type)
    Ras_Char -> (ty1 == Ras_Char) || (ty1 == Ras_Bottom_type)
    Ras_Bottom_type -> (ty1 == Ras_Bottom_type)
    _ -> False


tyinf expr = {- obtaining the type of expr, with type inference. -}
  case expr of
    Mediate_code_raw_Var var -> var_type var
    Mediate_code_raw_Literal c -> (case c of
                                     Char_const c' -> Ras_Char
                                     String_const c' -> Ras_String
                                     Numeric_const c' -> (case c' of
                                                            Ras_Integer_const c_i -> Ras_Integer
                                                            Ras_Real_const c_r -> Ras_Real) )
                                                            
    _ -> Ras_Unknown_type


typecheck (row, col) expr = {- Updating types of each sub-expr. in given expr, by type inference. -}
  case expr of
    {- If e1 : T1, e2 : T2, and T2 <: T1, then (e1:T1 := e2:T2) : T1. -}
    Mediate_code_raw_Bin {mnemonic = m}
      | m == Mn_asgn -> let lvalue = operand_0 expr
                            rvalue = operand_1 expr
                        in
                          case lvalue of
                            Mediate_code_raw_Var var -> let ty_l = tyinf lvalue
                                                            ty_r = tyinf rvalue
                                                        in
                                                          if (ty_l == Ras_Bottom_type) then
                                                            let lvalue' = Mediate_code_raw_Var var{var_type = ty_r}
                                                            in
                                                              (expr{operand_0 = lvalue'}, Nothing)
                                                          else
                                                            if (is_subtype ty_r ty_l) then (expr, Nothing)
                                                            else (expr, Just [(Par_error ((row, col), Tycon_mismatched))])
                            _ -> (expr, Just [(Par_error ((row, col), Compiler_internal_error))])
      | otherwise -> (expr, Nothing)
    _ -> (expr, Nothing)


data Sym_attr_type =
  Attrib_Var Mediate_var_attr
  | Attrib_Rec (String, [Ras_Record_field])
  | Attrib_Typedef Ras_Types
  deriving (Eq, Ord, Show)

data Sym_attrib =
  Sym_attrib {attr_decl :: Sym_attr_type, attr_fragment :: Mediate_code_fragment_raw}
  deriving (Eq, Ord, Show)

data Symtbl_node =
  Sym_entry {sym_ident :: String, sym_attrib :: Sym_attrib}
  deriving (Eq, Ord, Show)

data Sym_entity =
  Sym_var Mediate_var_attr
  | Sym_record (String, [Ras_Record_field])
    deriving (Eq, Ord, Show)

data Symtbl_cluster =
  Sym_empty
  | Sym_add Symtbl_node Symtbl_cluster
  deriving (Eq, Ord, Show)


data Symtbl_anon_ident =
  Symtbl_anon_ident {sym_anon_var :: Integer, sym_anon_record :: Integer}
  deriving (Eq, Ord, Show)

data Symtbl =
  Scope_empty
  | Scope_add (Int, Symtbl_anon_ident, Symtbl_cluster) Symtbl
  deriving (Eq, Ord, Show)


sym_search symtbl ident =
  let walk syms ident =
        case syms of
          Sym_empty -> Nothing
          Sym_add sym syms' -> if ((sym_ident sym) == ident) then Just (sym, syms')
                              else walk syms' ident
  in
    case symtbl of
      Scope_empty -> Nothing
      Scope_add (lv, anon_idents, syms) symtbl' ->
        (case (walk syms ident) of
            Just (found, syms') -> Just ((sym_attrib found), Scope_add (lv, anon_idents, syms') symtbl')
            Nothing -> sym_search symtbl' ident )


sym_lookup_var symtbl ident =
  let trying = sym_search symtbl ident
  in
    case trying of
      Nothing -> Nothing
      Just (attr@(Sym_attrib {attr_decl = decl_type}), remainders) -> (case decl_type of       
                                                                         Attrib_Var sig -> Just (sig, attr)
                                                                         _ -> sym_lookup_var remainders ident )

sym_lookup_rec symtbl ident =
  let trying = sym_search symtbl ident
  in
    case trying of
      Nothing -> Nothing
      Just (attr@(Sym_attrib {attr_decl = decl_type}), remainders) -> (case decl_type of
                                                                         Attrib_Rec (_, sig) -> Just (sig, attr)
                                                                         _ -> sym_lookup_rec remainders ident )


sym_lookup_type symtbl ident =
  let trying = sym_search symtbl ident
  in
    case trying of
      Nothing -> Nothing
      Just (attr@(Sym_attrib {attr_decl = decl_type}), remainders) -> (case decl_type of
                                                                         Attrib_Typedef ty -> Just (ty, attr)
                                                                         _ -> sym_lookup_type remainders ident )


walk_on_scope sym_cluster (kind, tgt_id) =
  let cmp_kind (Sym_entry {sym_attrib = attr}) =
        let attr_type = attr_decl attr
        in
          case kind of
            Sym_var _ -> (case attr_type of
                            Attrib_Var _ -> True
                            _ -> False )
            Sym_record _ -> (case attr_type of
                               Attrib_Rec _ -> True
                               _ -> False )
  in
    case sym_cluster of
      Sym_empty -> Nothing
      Sym_add sym sym_cluster' -> if ((cmp_kind sym) && ((sym_ident sym) == tgt_id)) then Just sym
                                  else walk_on_scope sym_cluster' (kind, tgt_id)

sym_regist ovwt symtbl entity fragment =
  let reg_sym ident sym =
        case symtbl of
          Scope_empty ->
            ((Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, (Sym_add sym Sym_empty)) Scope_empty), Nothing)
          Scope_add (lv, anon_ident_crnt, syms) symtbl' ->
            (case syms of
               Sym_empty -> ((Scope_add (lv, anon_ident_crnt, (Sym_add sym Sym_empty)) symtbl'), Nothing)
               Sym_add _ _ -> (case (walk_on_scope syms (entity, ident)) of
                                 Just e -> if (not ovwt) then (symtbl, Just Symbol_redifinition)
                                           else ((Scope_add (lv, anon_ident_crnt, (Sym_add sym syms)) symtbl'), Nothing)
                                 Nothing -> ((Scope_add (lv, anon_ident_crnt, (Sym_add sym syms)) symtbl'), Nothing)
                              )
            )
  in
  case entity of
    Sym_var decl@(Mediate_var_attr {var_ident = v_id}) ->
      let node = Sym_entry {sym_ident = v_id, sym_attrib = Sym_attrib {attr_decl = Attrib_Var decl, attr_fragment = fragment}}
      in
        reg_sym v_id node
    Sym_record (rec_ident, fields) ->
      let node = Sym_entry {sym_ident = rec_ident, sym_attrib = Sym_attrib {attr_decl = Attrib_Rec (rec_ident, fields), attr_fragment = fragment}}
      in
        reg_sym rec_ident node


{- data Sym_attrib =
  Attrib_Var {attr_type :: Ras_Types, attr_init :: Ras_Const, attr_fragment :: Mediate_code_fragment_raw}
  | Attrib_Rec {attr_decl :: [Ras_Record_field], attr_fragment :: Mediate_code_fragment_raw}
  deriving (Eq, Ord, Show)

sym_regist ovwt symtbl decl@Mediate_var_attr{var_ident = v_id, var_type = v_ty, var_const = v_ini_val} fragment =
  let node = Sym_entry {sym_ident = v_id, sym_attrib = Sym_attrib {attr_decl = Attrib_Var decl, attr_fragment = fragment}}
  in
    case symtbl of
      Scope_empty -> ((Scope_add (0, (Sym_add node Sym_empty)) Scope_empty), Nothing)
      Scope_add (lv, syms) symtbl' -> (case syms of
                                         Sym_empty -> ((Scope_add (lv, (Sym_add node Sym_empty)) symtbl'), Nothing)
                                         Sym_add _ _ -> (case (walk_on_scope syms v_id) of
                                                           Just e -> if (not ovwt) then (symtbl, Just Symbol_redifinition)
                                                                     else ((Scope_add (lv, (Sym_add node syms)) symtbl'), Nothing)
                                                           Nothing -> ((Scope_add (lv, (Sym_add node syms)) symtbl'), Nothing) )
                                      ) -}


enter_scope symtbl =
  case symtbl of
    Scope_empty -> Scope_add (0, Symtbl_anon_ident {sym_anon_var = 1, sym_anon_record = 1}, Sym_empty) Scope_empty
    Scope_add (lv, sym_anon_ident, _) _ -> Scope_add (lv + 1, sym_anon_ident, Sym_empty) symtbl


sym_anonid_var symtbl =
  let d2s_var m = "var_" ++ (show m)
  in
    let symtbl' = (case symtbl of
                     Scope_empty -> enter_scope symtbl
                     Scope_add _ _ -> symtbl )
    in
      case symtbl' of
        Scope_add (lv, anon_crnt@(Symtbl_anon_ident {sym_anon_var = crnt_top}), syms) symtbl'' ->
          ((d2s_var crnt_top), Scope_add (lv, anon_crnt {sym_anon_var = crnt_top + 1}, syms) symtbl'')


sym_anonid_rec symtbl =
  let d2s_rec m = "rec_" ++ (show m)
  in
    let symtbl' = (case symtbl of
                     Scope_empty -> enter_scope symtbl
                     Scope_add _ _ -> symtbl )
    in
      case symtbl' of
        Scope_add (lv, anon_crnt@(Symtbl_anon_ident {sym_anon_record = crnt_top}), syms) symtbl'' ->
          ((d2s_rec crnt_top), Scope_add (lv, anon_crnt {sym_anon_record = crnt_top + 1}, syms) symtbl'')


leave_scope symtbl =
  case symtbl of
    Scope_empty -> Scope_empty
    Scope_add sco symtbl' -> symtbl'


par_record symtbl (row, col) tokens =
  let decl_fields acc symtbl (row, col) tokens =
        let decl_type symtbl tokens =
              case tokens of
                (_, BOOLEAN):ts -> (Ras_Boolean, symtbl, ts, Nothing)
                (_, INTEGER):ts -> (Ras_Integer, symtbl, ts, Nothing)
                (_, REAL):ts -> (Ras_Real, symtbl, ts, Nothing)
                (_, STRING):ts -> (Ras_String, symtbl, ts, Nothing)
                (_, CHAR):ts -> (Ras_Char, symtbl, ts, Nothing)
                ((row, col), RECORD):ts -> (case (par_record symtbl (row, col) ts) of
                                              (r_ident, symtbl', ts', Nothing) ->
                                                (case (sym_lookup_rec symtbl' r_ident) of
                                                   Just (sig, attr) -> (Ras_Record (r_ident, sig), symtbl', ts', Nothing)
                                                   Nothing -> (Ras_Unknown_type, symtbl', ts', Just [(Par_error ((row, col), Compiler_internal_error))]) )
                                              (_, symtbl', ts', err) -> (Ras_Illformed_type, symtbl', ts', err)
                                           )
                {-((row, col), IDENT t_ident):ts -> (case (sym_lookup_type symtbl t_ident) of
                                                     Just (sig, attr) -> (Ras_DefType sig, symtbl, ts, Nothing)
                                                     Nothing -> (Ras_Unknown_type, symtbl, ts, Just [(Par_error ((row, col), Illformed_Declarement))]) ) -}
                ((row, col), _):ts -> (Ras_Illformed_type, symtbl, tokens, Just [(Par_error ((row, col), Illformed_Declarement))])
        in
          case tokens of
            ((row, col), IDENT f_ident):ts ->
              let field = Ras_Record_field {memb_ident = f_ident, memb_type = Ras_Unknown_type}
              in
                (case ts of
                   ((row', col'), COLON):ts' -> (case (decl_type symtbl ts') of
                                                   (f_type, symtbl', ts', err) ->
                                                     let acc' = acc ++ [field{memb_type = f_type}]
                                                     in
                                                       case err of
                                                         Nothing -> (case ts' of
                                                                       ((row'', col''), SEMICOL):ts'' -> decl_fields acc' symtbl' (row'', col'') ts''
                                                                       _ -> (acc', symtbl', ts', Nothing) )
                                                         _ -> (acc', symtbl', ts', err)
                                                )
                   ((row', col'), _):ts' -> ((acc ++ [field]), symtbl, ts, Just [(Par_error ((row', col'), Illformed_Declarement))])
                   _ -> ((acc ++ [field]), symtbl, [], Just [(Par_error ((row, col), Illformed_Declarement))])
                )
            ((row, col), _):ts -> (acc, symtbl, tokens, Just [(Par_error ((row, col), Illformed_Declarement))])
            _ -> (acc, symtbl, [], Just [(Par_error ((row, col), Illformed_Declarement))])
  in
    let (r_ident, symtbl')  = sym_anonid_rec symtbl
    in
      case tokens of
        ((row, col), LBRA):ts' -> (case (decl_fields [] symtbl' (row, col) ts') of
                                      (fields, symtbl', tokens', Nothing) ->
                                        (case tokens' of
                                           ((row', col'), RBRA):ts'' ->
                                             (case (sym_regist False symtbl' (Sym_record (r_ident, fields)) Mediate_code_fragment_raw_None) of
                                                (symtbl', Nothing) -> (r_ident , symtbl', ts'', Nothing)
                                                (symtbl', Just err) -> (r_ident , symtbl', ts'', Just [(Par_error ((row, col), err))]) )
                                           ((row', col'), _):ts'' -> (r_ident , symtbl', tokens',Just [(Par_error ((row', col'), Illformed_Declarement))])
                                        )
                                      (fields, symtbl', tokens', err) -> (r_ident, symtbl', tokens', err)
                                  )
        _ -> (r_ident, symtbl', tokens, Just [(Par_error ((row, col), Illformed_Declarement))])


par_init_on_decl symtbl vars (((row0, col0), tk0):tokens) =
  case vars of
    [] -> (symtbl, [], tokens, Nothing)
    (v@(Mediate_code_raw_Var v_attr)):vs ->
      case (var_type v_attr) of
        Ras_Record (_, _) -> (symtbl, vars, tokens, Nothing)
        _ -> let pairing val =
                   case val of
                     Mediate_code_raw_Var v@(Mediate_var_attr {var_attr = v_attr}) ->
                       (case v_attr of
                          Var_attr_const c -> let lvalue = val
                                                  rvalue = Mediate_code_raw_Literal c
                                              in
                                                Mediate_code_raw_Bin {mnemonic = Mn_asgn, operand_0 = lvalue, operand_1 = rvalue}
                          _ -> assert False val
                       )
                     _ -> val
                 
                 folding exprs =
                   let strip expr =
                         case expr of
                           Mediate_code_raw_Bin {operand_0 = lvalue} -> lvalue
                           _ -> assert False expr
                   in
                     case exprs of
                       [] -> ([], Nothing)
                       (e, err):es -> (case (folding es) of
                                         (es', _) -> (((strip e):es'), err) )
                 
                 def_and_reg_vars symtbl (vars, errs) =
                   case vars of
                     [] -> (symtbl, [], errs)
                     (v@(Mediate_code_raw_Var var)):vs ->
                       let (symtbl', r) = sym_regist True symtbl (Sym_var var) v
                       in
                         case r of
                           Nothing -> (case (def_and_reg_vars symtbl' (vs, errs)) of
                                         (symtbl', vars', errs') -> (symtbl', v:vars', errs') )
                           Just sym_err -> let errs' = add_error errs (Par_error ((var_coord var), sym_err))
                                           in
                                             def_and_reg_vars symtbl' (vs, errs')
             in
               let init c = pairing . (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_attr = Var_attr_const c}))
               in
                 case (case tokens of
                         ((row, col), (CHR_CONST c)):ts -> (def_and_reg_vars symtbl (folding (map ((typecheck (row, col)) . (init (Char_const c))) vars)), ts)
                         ((row, col), (STR_CONST s)):ts -> (def_and_reg_vars symtbl (folding (map ((typecheck (row, col)) . (init (String_const s))) vars)), ts)
                         ((row, col), (NUM_CONST n)):ts -> (def_and_reg_vars symtbl (folding (map ((typecheck (row, col)) . (init (Numeric_const n))) vars)), ts)
                         ((row, col), _):ts -> ((symtbl, vars, Just [(Par_error ((row, col), Illformed_Declarement))]), tokens) ) of
                   ((symtbl', vars', err), tokens') -> (symtbl', vars, tokens', err)


par_record_const acc symtbl (r_ident, fields) tokens@((tk@((row, col), _)):ts) =
  case fields of
    [] -> (case ts of
             (_, RBRA):ts' -> (acc, symtbl, ts', Nothing)
             ((row, col), _):ts' -> (acc, symtbl, ts, Just [Par_error ((row, col), Illformed_Declarement)])
             _ -> (acc, symtbl, [], Just [Par_error ((row, col), Illformed_Declarement)])
          )
    f:fs ->
      (case (memb_type f) of
         Ras_Record (r_nested_ident, r_nested_fields) ->
           (case ts of
              ((row', col'), LBRA):ts' ->
                (case (par_record_const [] symtbl (r_nested_ident, r_nested_fields) ts) of
                   (acc_nested, symtbl', tokens', err) -> let acc' = acc ++ [Mediate_code_raw_Var (Mediate_var_attr {var_ident = (memb_ident f),
                                                                                                                     var_type = (memb_type f),
                                                                                                                     var_attr = (Var_attr_fields acc_nested)})]
                                                          in
                                                            case err of
                                                              Nothing -> tailing fs (acc', symtbl', tokens', err)
                                                              Just _ -> (acc', symtbl', tokens', err)
                )
              ((row', col'), _):ts' -> (acc, symtbl, ts, Just [Par_error ((row', col'), Illformed_Declarement)])
              _ -> (acc, symtbl, [], Just [Par_error ((row, col), Illformed_Declarement)])
           )
         {- Ras_Typedef ty_ident -> -}
         _ -> let v_memb = Mediate_code_raw_Var (Mediate_var_attr {var_ident = (memb_ident f), var_type = (memb_type f),
                                                                   var_attr = (Var_attr_const Ras_Const_not_defined)})a
              in
                case (tychk_and_init [v_memb] ts) of
                  (((Mediate_code_raw_Bin {operand_0 = v_memb'}):es, err), tokens') -> let acc' = acc ++ [v_memb']
                                                                                       in
                                                                                         tailing fs (acc', symtbl, tokens', err)
                  ((_, err), tokens') -> ((acc ++ [v_memb]), symtbl, tokens', err)
      )
      
      where tailing fields' (acc', symtbl', tokens', err) =
              let padding omits =
                    case omits of
                      [] -> []
                      f:fs -> (case (memb_type f) of
                                 Ras_Record (r_ident, r_fields) ->
                                   Mediate_code_raw_Var (Mediate_var_attr {var_ident = (memb_ident f), var_type = (memb_type f),
                                                                           var_attr = Var_attr_fields (padding r_fields)})
                                 Ras_Typedef ty_ident ->
                                   let (ty_def, _) = sym_lookup_type symtbl' ty_ident
                                   in
                                     {- Here!: [ty_def] isn't fields list, but LIST of Ras_Types. -}
                                     case (padding [ty_def]) of
                                       p:ps -> assert (ps == []) (Mediate_code_raw_Var (Mediate_var_attr {var_ident = (memb_ident f), var_type = (memb_type f),
                                                                                                          var_attr = Var_attr_typedef p}) )
                                 _ -> Mediate_code_raw_Var (Mediate_var_attr {var_ident = (memb_ident f), var_type = (memb_type f),
                                                                              var_attr = Var_attr_const Ras_Const_not_defined})
                              ) : (padding fs)
              in
                case err of
                  Nothing -> (case fields' of
                                [] -> (case tokens' of
                                         (_, SEMICOL):(_, RBRA):ts' -> (acc', symtbl', ts', Nothing)
                                         (_, RBRA):ts' -> (acc', symtbl', ts', Nothing)
                                         ((row', col'), _):ts' -> (acc', symtbl', tokens', Just [Par_error ((row', col'), Illformed_Declarement)])
                                         _ -> (acc', symtbl', [], Just [Par_error ((row, col), Illformed_Declarement)])
                                      )
                                _ -> (case tokens' of
                                        (_, SEMICOL):(_, RBRA):ts' -> ((acc' ++ (padding fields')), symtbl', ts', Nothing)
                                        (_, RBRA):ts' -> ((acc' ++ (padding fields')), symtbl', ts', Nothing)
                                        (_, SEMICOL):ts' -> par_record_const acc' symtbl' (r_ident, fields') tokens'
                                        ((row', col'), _):ts' -> ((acc' ++ (padding fields')), symtbl', tokens', Just [Par_error ((row', col'), Illformed_Declarement)])
                                        _ -> ((acc' ++ (padding fields')), symtbl', [], Just [Par_error ((row, col), Illformed_Declarement)])
                                     )
                             )
                  Just _ -> (acc', symtbl', tokens', err)


par_var acc symtbl (row, col) tokens =
  let init_and_tychk var_ty vars tokens =
        let folding val =
              case val of
                Mediate_code_raw_Var v ->
                  let lvalue = Mediate_code_raw_Var v
                      rvalue = Mediate_code_raw_Literal (var_const v)
                  in
                    Mediate_code_raw_Bin {mnemonic = Mn_asgn, operand_0 = lvalue, operand_1 = rvalue}
                _ -> val
        in
          let def_and_reg symtbl [] = (symtbl, [])
              def_and_reg symtbl ((Mediate_code_raw_Bin {operand_0 = lvalue}):es) = (case lvalue of
                                                                                       Mediate_code_raw_Var var ->
                                                                                         let (symtbl', r) = sym_regist False symtbl (Sym_var var) lvalue
                                                                                         in
                                                                                           (case r of
                                                                                              Nothing -> (case (def_and_reg symtbl' es) of
                                                                                                            (symtbl', es') -> (symtbl', lvalue:es') )
                                                                                              Just err -> def_and_reg symtbl es )
                                                                                       _ -> def_and_reg symtbl es
                                                                                    )
          in
            case tokens of
              ((row, col), DEF):ts -> (case ts of
                                         ((row', col'), (CHR_CONST c)):ts' ->
                                           let rs = map (typecheck (row', col') . folding . (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_const = Char_const c}))) vars
                                           in
                                             (case rs of
                                                ((Mediate_code_raw_Bin {mnemonic = m, operand_0 = var', operand_1 = c'}), Nothing):rs'
                                                  | c' == (Mediate_code_raw_Literal (Char_const c)) -> (case (def_and_reg symtbl (map fst rs)) of
                                                                                                          (symtbl', vars') -> (vars', symtbl', ts', Nothing) )
                                                  | otherwise -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Compiler_internal_error))])
                                                _ -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Illformed_Declarement))])
                                             )
                                         ((row', col'), (STR_CONST c)):ts' ->
                                           let rs = map (typecheck (row', col') . folding . (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_const = String_const c}))) vars
                                           in
                                             (case rs of
                                                ((Mediate_code_raw_Bin {mnemonic = m, operand_0 = var', operand_1 = c'}), Nothing):rs'
                                                  | c' == (Mediate_code_raw_Literal (String_const c)) -> (case (def_and_reg symtbl (map fst rs)) of
                                                                                                            (symtbl', vars') -> (vars', symtbl', ts', Nothing) )
                                                  | otherwise -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Compiler_internal_error))])
                                                _ -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Illformed_Declarement))])
                                             )
                                         ((row', col'), (NUM_CONST c)):ts' ->
                                           let rs = map (typecheck (row', col') . folding  . (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_const = Numeric_const c}))) vars
                                           in
                                             (case rs of
                                                ((Mediate_code_raw_Bin {mnemonic = m, operand_0 = var', operand_1 = c'}), Nothing):rs'
                                                  | c' == (Mediate_code_raw_Literal (Numeric_const c)) -> (case (def_and_reg symtbl (map fst rs)) of
                                                                                                             (symtbl', vars') -> (vars', symtbl', ts', Nothing) )
                                                  | otherwise -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Compiler_internal_error))])
                                                _ -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Illformed_Declarement))])
                                             )
                                         ((row', col'), LBRA):ts' ->
                                           (case var_ty of
                                              Ras_Record (r_ident, r_fields) -> (case (par_record_const [] symtbl (r_ident, r_fields) ts) of
                                                                                   (fields, symtbl', tokens', err) ->
                                                                                     let vars' =  map (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_fields = fields})) vars
                                                                                     in
                                                                                       (vars', symtbl', tokens', err) )
                                              _ -> (vars, symtbl, ts', Just [(Par_error ((row', col'), Illformed_Declarement))])
                                           )
                                         _ -> (vars, symtbl, ts, Just [(Par_error ((row, col), Illformed_Declarement))])
                                      )
              _ -> (case (def_and_reg symtbl (map folding vars)) of
                     (symtbl', vars') -> (vars', symtbl', tokens, Nothing) )
  in
    case tokens of
      [] -> (acc, symtbl, [], Just [(Par_error ((row, col), Illformed_Declarement))])
      t:ts -> (case t of
                 ((row, col), IDENT v_ident) ->
                   let vars = acc ++ [Mediate_code_raw_Var (Mediate_var_attr {var_ident = v_ident,
                                                                              var_type = Ras_Bottom_type,
                                                                              var_const = Ras_Const_not_defined})]
                   in
                     case ts of
                       t':ts' -> (case t' of
                                    ((row', col'), COMMA) -> par_var vars symtbl (row', col') ts'
                                    ((row', col'), TYPED_AS) -> (case ts' of
                                                                   u:us -> let reveal ty vars = map (\(Mediate_code_raw_Var v) -> Mediate_code_raw_Var (v{var_type = ty})) vars
                                                                           in
                                                                             (case u of
                                                                                (_, BOOLEAN) -> init_and_tychk Ras_Boolean (reveal Ras_Boolean vars) us
                                                                                (_, INTEGER) -> init_and_tychk Ras_Integer (reveal Ras_Integer vars) us
                                                                                (_, REAL) -> init_and_tychk Ras_Real (reveal Ras_Real vars) us
                                                                                (_, STRING) -> init_and_tychk Ras_String (reveal Ras_String vars) us
                                                                                (_, CHAR) -> init_and_tychk Ras_Char (reveal Ras_Char vars) us
                                                                                ((row'', col''), RECORD) ->
                                                                                  (case (par_record symtbl (row'', col'') us) of
                                                                                     (r_ident, symtbl', us', err) ->
                                                                                       (case err of
                                                                                          Nothing ->
                                                                                            let vars = acc ++ [Mediate_code_raw_Var (Mediate_rec_attr {var_ident = v_ident,
                                                                                                                                                       var_type = Ras_Bottom_type,
                                                                                                                                                       var_fields = []})]
                                                                                            in
                                                                                              (case (sym_lookup_rec symtbl' r_ident) of
                                                                                                 Just (r_fields, _) -> let r_type = Ras_Record (r_ident, r_fields)
                                                                                                                       in
                                                                                                                         init_and_tychk r_type (reveal r_type vars) us'
                                                                                                 Nothing -> (vars, symtbl', us', Just [(Par_error ((row', col'), Compiler_internal_error))]) )
                                                                                          _ -> (vars, symtbl', us', err) )
                                                                                  )
                                                                                ((row'', col''), _) -> (acc, symtbl, us, Just [(Par_error ((row'', col''), Illformed_Declarement))])
                                                                             )
                                                                   _ -> (vars, symtbl, [], Just [(Par_error ((row', col'), Illformed_Declarement))])
                                                                )
                                    -- _ -> (vars, symtbl, ts, Nothing)
                                    _ -> init_and_tychk Ras_Bottom_type vars ts
                                 )
                       -- _ -> (vars, symtbl, [], Nothing)
                       _ -> init_and_tychk Ras_Bottom_type vars []
              ):


par_expr symtbl tokens = (Mediate_code_fragment_raw_None, symtbl, tokens, Nothing)


par_asgn symtbl ((row, col), ident) tokens =
  -- (symtbl, [], tokens)
  case (sym_lookup_var symtbl ident) of
    Just (sig, attr) ->
      let fr_asgn = Mediate_code_raw_Bin {mnemonic = Mn_asgn, operand_0 = (attr_fragment attr), operand_1 = Mediate_code_fragment_raw_None}
      in
        (case tokens of
           [] -> ([fr_asgn], symtbl, [], Just [(Par_error ((row, col), Expr_no_asgn))])
           ((row', col'), ASGN):ts ->
             let update symtbl expr_asgn@(Mediate_code_raw_Bin {operand_0 = lvalue}) =
                   case lvalue of
                     Mediate_code_raw_Var var -> let (symtbl', r) = sym_regist True symtbl (Sym_var var) lvalue
                                                 in
                                                   (case r of
                                                      Nothing -> (expr_asgn, symtbl', Nothing)
                                                      Just err -> (expr_asgn, symtbl', Just [(Par_error ((row, col), Compiler_internal_error))])
                                                   )
                     _ -> (expr_asgn, symtbl, Just [(Par_error ((row, col), Compiler_internal_error))])
             in
               (case (par_expr symtbl ts) of
                  (expr_r, symtbl', ts', r) -> let fr_asgn' = fr_asgn{operand_1 = expr_r}
                                               in
                                                 if (r == Nothing) then
                                                   (case (typecheck (row, col) fr_asgn') of
                                                      (fr_asgn', Nothing) -> (case (update symtbl fr_asgn') of
                                                                                (fr_asgn', symtbl', r) -> ([fr_asgn'], symtbl', ts', r) )
                                                      (fr_asgn', r) -> ([fr_asgn'], symtbl', ts', r)
                                                   )
                                                 else ([fr_asgn'], symtbl', ts', r)
               )
           _ -> ([fr_asgn], symtbl, tokens, Just [(Par_error ((row, col), Expr_no_asgn))])
        )
    Nothing ->
      let fr_asgn = Mediate_code_raw_Bin {mnemonic = Mn_asgn, operand_0 = Mediate_code_fragment_raw_None, operand_1 = Mediate_code_fragment_raw_None}
      in
        (case tokens of
           [] -> ([fr_asgn], symtbl, [], Just [(Par_error ((row, col), Expr_no_asgn))])
           ((row', col'), ASGN):ts -> (case (par_expr symtbl ts) of
                                         (expr_r, symtbl', ts', r) -> ([fr_asgn{operand_1 = expr_r}], symtbl', ts', r) )
           _ -> ([fr_asgn], symtbl, tokens, Just [(Par_error ((row, col), Expr_no_asgn))])
        )


ras_parse forest symtbl tokens error =
  let panicked ts =
        case ts of
          [] -> []
          (_, tk_code):ts -> if (tk_code == SEMICOL) then ts else (panicked ts)
  in
    case tokens of
      [] -> (forest, symtbl, [], error)
      t:ts -> case t of
                -- ((r, c), RECORD) -> 
                ((r, c), VAR) -> go_on (par_var [] symtbl (r, c) ts)
                ((r, c), IDENT v_ident) -> go_on (par_asgn symtbl ((r, c), v_ident) tokens)
                _ -> ras_parse forest symtbl (panicked tokens) error
                
                where
                  go_on (fragments, symtbl', ts', err) =
                    let forest' = forest ++ fragments
                    in
                      case err of
                        Nothing -> (case ts' of
                                      (_, u_tk):us -> let us' = if (u_tk == SEMICOL) then us else ts'
                                                      in
                                                        ras_parse forest' symtbl' us' error
                                      _ -> (forest', symtbl', [], error) )
                        Just _ -> ras_parse forest' symtbl' (panicked ts') (append_error error err)


main src =
  let lexicon = [("and", AND), ("array", ARRAY), ("begin", BEGIN), ("boolean", BOOLEAN), ("case", CASE),
                 ("char", CHAR), ("const", CONST), ("div", DIV), ("do", DO), ("downto", DOWNTO),
                 ("else", ELSE), ("end", END), ("file", FILE), ("for", FOR),
                 ("function", FUNCTION), ("goto", GOTO), ("if", IF), ("in", IN), ("Integer", INTEGER),
                 ("label", LABEL), ("mod", MOD), ("nil", NIL), ("not", NOT),
                 ("of", OF), ("or", OR), ("packed", PACKED), ("procedure", PROCEDURE),
                 ("program", PROGRAM), ("real", REAL), ("record", RECORD), ("Real", REAL), ("repeat", REPEAT), ("set", SET),
                 ("String", STRING), ("then", THEN), ("to", TO), ("type", TYPE), ("until", UNTIL),
                 ("var", VAR), ("while", WHILE), ("with", WITH)]
  in
    do tokens <- (case (lex_main lexicon (1,1) src) of
                    [] -> Nothing
                    ts -> if ( (length ts) > (length (lex_purge ts)) ) then Nothing else Just ts )
--       return (par_real_const PHONY tokens)
       tokens' <- return (par_real_const ((-1, -1), PHONY) tokens)
       return (ras_parse [] Scope_empty tokens' Nothing)
       
       where
         lex_purge tokens = case tokens of
                              [] -> []
                              (_, SKIPPED _):ts -> lex_purge ts
                              (t:ts) -> t:(lex_purge ts)
