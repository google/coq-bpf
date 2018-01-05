(* Copyright 2017 Google LLC

Licensed under the Apache License, Version 2.0 (the "License"); you may not use
this file except in compliance with the License. You may obtain a copy of the
License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied. See the License for the
specific language governing permissions and limitations under the License. *)

Set Primitive Projections.
Set Printing Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Init.Peano.
Require Import Coq.Lists.List.
Require Coq.ZArith.Zdiv.

Fixpoint set_nth {T} (ls : list T) (n : nat) (x : T) {struct n} : list T :=
  match ls with
  | nil => nil
  | x'::ls' =>
    match n with
    | O => x::ls'
    | S n' => x' :: set_nth ls' n' x
    end
  end.

Module word.
  Record word :=
    {
      T :> Type;
      zero : T;

      eqb : T -> T -> bool;
      geb : T -> T -> bool;
      gtb : T -> T -> bool;

      lor : T -> T -> T;
      land : T -> T -> T;
      shiftl : T -> T -> T;
      shiftr : T -> T -> T;

      add : T -> T -> T;
      sub : T -> T -> T;
      opp : T -> T;
      mul : T -> T -> T;
      div : T -> T -> T; 

      to_nat : T -> nat;
      of_nat : nat -> T;
    }.
End word.

Module word_Z.
  Section word_Z.
    Import BinInt Zdiv Logic. Local Open Scope Z_scope.
    Context {n : Z}.
    Let T := { z : Z | z mod (2^n) = z }.
    Let zero : T. refine (exist _ 0 _). apply Zmod_0_l. Defined.

    Let eqb (x y : T) : bool := Z.eqb (proj1_sig x) (proj1_sig y).
    Let geb (x y : T) : bool := Z.geb (proj1_sig x) (proj1_sig y).
    Let gtb (x y : T) : bool := Z.gtb (proj1_sig x) (proj1_sig y).

    Let admit : forall {T}, T. Admitted.

    Let lor (x y : T) : T := exist _ (Z.lor (proj1_sig x) (proj1_sig y)) admit.
    Let land (x y : T) : T := exist _ (Z.land (proj1_sig x) (proj1_sig y)) admit.
    Let shiftl (x y : T) : T := exist _ (Z.shiftl (proj1_sig x) (proj1_sig y)) admit.
    Let shiftr (x y : T) : T := exist _ (Z.shiftr (proj1_sig x) (proj1_sig y)) admit.

    Let add (x y : T) : T := exist _ (Z.add (proj1_sig x) (proj1_sig y)) admit.
    Let sub (x y : T) : T := exist _ (Z.sub (proj1_sig x) (proj1_sig y)) admit.
    Let opp (x : T) : T := exist _ (Z.opp (proj1_sig x)) admit.
    Let mul (x y : T) : T := exist _ (Z.mul (proj1_sig x) (proj1_sig y)) admit.
    Let div (x y : T) : T := exist _ (Z.div (proj1_sig x) (proj1_sig y)) admit.

    Let to_nat (x : T) : nat := Z.to_nat (proj1_sig x).
    Let of_Z (x : Z) : T := exist _ (Z.land x (Z.ones n)) admit.
    Let of_nat (x : nat) : T := of_Z (Z.of_nat x).

    Definition word := 
    {|
      word.T := T;
      word.zero := zero;

      word.eqb := eqb;
      word.geb := geb;
      word.gtb := gtb;

      word.lor := lor;
      word.land := land;
      word.shiftl := shiftl;
      word.shiftr := shiftr;

      word.add := add;
      word.sub := sub;
      word.opp := opp;
      word.mul := mul;
      word.div := div;

      word.to_nat := to_nat;
      word.of_nat := of_nat
    |}.
  End word_Z.
  Arguments word : clear implicits.
End word_Z.

(* TODO: parametrize over uint* -- Coq crashes on printing execute_instruction outside section *)
Import word.
Definition uint8 := word_Z.word (BinInt.Z.of_nat 8).
Definition uint16 := word_Z.word (BinInt.Z.of_nat 16).
Definition uint32 := word_Z.word (BinInt.Z.of_nat 32).

Structure instruction :=
  {
    code : uint16;
    jt : uint8;
    jf : uint8;
    k : uint32
  }.

Structure state :=
  {
    A : uint32;
    X : uint32;
    mem : list uint32;
  }.

Notation "( s 'with' 'A'   := a )" := ({|A := a;     X := s.(X); mem := s.(mem)|}).
Notation "( s 'with' 'X'   := x )" := ({|A := s.(A); X := x    ; mem := s.(mem)|}).
Notation "( s 'with' 'mem' := m )" := ({|A := s.(A); X := s.(X); mem := m      |}).

Local Open Scope nat_scope.
(*
 * The instruction encodings.
 *)
(* instruction classes *)
(* #define BPF_CLASS(code) ((code) & 0x07) *)
Notation		BPF_LD	:= (uint16.(of_nat) 0).
Notation		BPF_LDX	:= (uint16.(of_nat) 1).
Notation		BPF_ST	:= (uint16.(of_nat) 2).
Notation		BPF_STX	:= (uint16.(of_nat) 3).
Notation		BPF_ALU	:= (uint16.(of_nat) 4).
Notation		BPF_JMP	:= (uint16.(of_nat) 5).
Notation		BPF_RET	:= (uint16.(of_nat) 6).
Notation		BPF_MISC:= (uint16.(of_nat) 7).

(* ld/ldx fields *)
(* #define BPF_SIZE(code)	((code) & 0x18) *)
Notation		BPF_W	:= (uint16.(of_nat) (0*16+0)).
Notation		BPF_H	:= (uint16.(of_nat) (0*16+8)).
Notation		BPF_B	:= (uint16.(of_nat) (1*16+0)).
(* #define BPF_MODE(code)	((code) & 0xe0) *)
Notation		BPF_IMM	:=  (uint16.(of_nat) (0*16+0)).
Notation		BPF_ABS	:=  (uint16.(of_nat) (2*16+0)).
Notation		BPF_IND	:=  (uint16.(of_nat) (4*16+0)).
Notation		BPF_MEM	:=  (uint16.(of_nat) (6*16+0)).
Notation		BPF_LEN	:=  (uint16.(of_nat) (8*16+0)).
Notation		BPF_MSH	:=  (uint16.(of_nat) (10*16+0)).

(* alu/jmp fields *)
(* #define BPF_OP(code)	((code)& 0xf0) *)
Notation		BPF_ADD	:= (uint16.(of_nat) (0*16+0)).
Notation		BPF_SUB	:= (uint16.(of_nat) (1*16+0)).
Notation		BPF_MUL	:= (uint16.(of_nat) (2*16+0)).
Notation		BPF_DIV	:= (uint16.(of_nat) (3*16+0)).
Notation		BPF_OR	:= (uint16.(of_nat) (4*16+0)).
Notation		BPF_AND	:= (uint16.(of_nat) (5*16+0)).
Notation		BPF_LSH	:= (uint16.(of_nat) (6*16+0)).
Notation		BPF_RSH	:= (uint16.(of_nat) (7*16+0)).
Notation		BPF_NEG	:= (uint16.(of_nat) (8*16+0)).
Notation		BPF_JA	:= (uint16.(of_nat) (0*16+0)).
Notation		BPF_JEQ	:= (uint16.(of_nat) (1*16+0)).
Notation		BPF_JGT	:= (uint16.(of_nat) (2*16+0)).
Notation		BPF_JGE	:= (uint16.(of_nat) (3*16+0)).
Notation		BPF_JSET:= (uint16.(of_nat) (4*16+0)).
(* #define BPF_SRC(code)	((code) & 0x08) *)
Notation		BPF_K	:= (uint16.(of_nat) 0).
Notation		BPF_X	:= (uint16.(of_nat) 8).

(* ret - BPF_K and BPF_X also apply *)
(* #define BPF_RVAL(code)((code) & 0x18) *)
Notation		BPF_A	:= (uint16.(of_nat) (1*16+0)).

(* misc *)
(* #define BPF_MISCOP(code) ((code) & 0xf8) *)
Notation		BPF_TAX	:= (uint16.(of_nat) (0*16+0)).
Notation		BPF_TXA	:= (uint16.(of_nat) (8*16+0)).

Notation BPF_MEMWORDS := 16.

(* "|" is already used for pattern-matching *)
Infix ".|" := (lor _) (at level 50) : nat_scope. 
Infix ".&" := (land _) (at level 50) : nat_scope. 
Infix "==" := (eqb _) (at level 70, no associativity) : nat_scope.


Section with_loaders.
  Context (wirelen : uint32).
  Context (ldb : uint32 -> option uint32).
  Context (ldh : uint32 -> option uint32).
  Context (ldw : uint32 -> option uint32).
  
  (* BPF interpreter, in continuation-passing style to make partial evaluation work nicely *)
  Definition execute_instruction {R} (i:instruction) (s:state) (done:uint32->R) (step:state->R) (jump:nat->R) : R :=
    let nz8 x := negb (uint8.(eqb) uint8.(zero) x) in
    let nz16 x := negb (uint16.(eqb) uint16.(zero) x) in
    let nz32 x := negb (uint32.(eqb) uint32.(zero) x) in
    let jump8 x := jump (uint8.(to_nat) x) in
    let jump16 x := jump (uint16.(to_nat) x) in
    let jump32 x := jump (uint32.(to_nat) x) in
         if i.(code) == (BPF_RET.|BPF_K) then done i.(k)
    else if i.(code) == (BPF_RET.|BPF_A) then done s.(A)
    else if i.(code) == (BPF_LD.|BPF_W.|BPF_ABS) then
           match ldw i.(k) with None => done uint32.(zero) | Some w => step (s with A := w) end
    else if i.(code) == (BPF_LD.|BPF_H.|BPF_ABS) then
           match ldh i.(k) with None => done uint32.(zero) | Some w => step (s with A := w) end
    else if i.(code) == (BPF_LD.|BPF_B.|BPF_ABS) then
           match ldb i.(k) with None => done uint32.(zero) | Some w => step (s with A := w) end
    else if i.(code) == (BPF_LD.|BPF_W.|BPF_LEN) then step (s with A := wirelen)
    else if i.(code) == (BPF_LDX.|BPF_W.|BPF_LEN) then step (s with X := wirelen)
    else if i.(code) == (BPF_LD.|BPF_W.|BPF_IND) then
           let k := uint32.(add) s.(X) i.(k) in
           match ldw k with None => done uint32.(zero) | Some w => step (s with A := w) end
    else if i.(code) == (BPF_LD.|BPF_H.|BPF_IND) then
           let k := uint32.(add) s.(X) i.(k) in
           match ldh k with None => done uint32.(zero) | Some w => step (s with A := w) end
    else if i.(code) == (BPF_LD.|BPF_B.|BPF_IND) then
           let k := uint32.(add) s.(X) i.(k) in
           match ldb k with None => done uint32.(zero) | Some w => step (s with A := w) end
    else if i.(code) == (BPF_LDX.|BPF_MSH.|BPF_B) then
           match ldb i.(k) with
           | None => done uint32.(zero)
           | Some X =>
                  let X := uint32.(land) X (uint32.(of_nat) 15) in 
                  let X := uint32.(shiftl) X (uint32.(of_nat) 2) in
                  step (s with X := X)
           end
    else if i.(code) == (BPF_LD.|BPF_IMM) then step (s with A := i.(k))
    else if i.(code) == (BPF_LDX.|BPF_IMM) then step (s with X := i.(k))
    else if i.(code) == (BPF_LD.|BPF_MEM) then step (s with A := List.nth_default uint32.(zero) s.(mem) (uint32.(to_nat) i.(k)))
    else if i.(code) == (BPF_LDX.|BPF_MEM) then step (s with X := List.nth_default uint32.(zero) s.(mem) (uint32.(to_nat) i.(k)))
    else if i.(code) == (BPF_ST ) then step (s with mem := (set_nth s.(mem) (uint32.(to_nat) i.(k)) s.(A)))
    else if i.(code) == (BPF_STX) then step (s with mem := (set_nth s.(mem) (uint32.(to_nat) i.(k)) s.(X)))
    else if i.(code) == (BPF_JMP.|BPF_JA) then jump32 i.(k)
    else if i.(code) == (BPF_JMP.|BPF_JGT.|BPF_K) then (if uint32.(gtb) s.(A) i.(k) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JGE.|BPF_K) then (if uint32.(geb) s.(A) i.(k) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JEQ.|BPF_K) then (if uint32.(eqb) s.(A) i.(k) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JSET.|BPF_K) then (if nz32(s.(A) .& i.(k)) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JGT.|BPF_X) then (if uint32.(gtb) s.(A) s.(X) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JGE.|BPF_X) then (if uint32.(geb) s.(A) s.(X) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JEQ.|BPF_X) then (if (s.(A) == s.(X)) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_JMP.|BPF_JSET.|BPF_X) then (if nz32(s.(A) .& s.(X)) then jump8 i.(jt) else jump8 i.(jf))
    else if i.(code) == (BPF_ALU.|BPF_ADD.|BPF_X) then step (s with A := uint32.(add) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_SUB.|BPF_X) then step (s with A := uint32.(sub) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_MUL.|BPF_X) then step (s with A := uint32.(mul) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_DIV.|BPF_X) then
      if s.(X) == uint32.(zero) then done uint32.(zero) else step (s with A := uint32.(div) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_AND.|BPF_X) then step (s with A := uint32.(land) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_OR .|BPF_X) then step (s with A := uint32.(lor) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_LSH.|BPF_X) then step (s with A := uint32.(shiftl) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_RSH.|BPF_X) then step (s with A := uint32.(shiftr) s.(A) s.(X))
    else if i.(code) == (BPF_ALU.|BPF_ADD.|BPF_K) then step (s with A := uint32.(add) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_SUB.|BPF_K) then step (s with A := uint32.(sub) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_MUL.|BPF_K) then step (s with A := uint32.(mul) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_DIV.|BPF_K) then step (s with A := uint32.(div) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_AND.|BPF_K) then step (s with A := uint32.(land) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_OR .|BPF_K) then step (s with A := uint32.(lor) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_LSH.|BPF_K) then step (s with A := uint32.(shiftl) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_RSH.|BPF_K) then step (s with A := uint32.(shiftr) s.(A) i.(k))
    else if i.(code) == (BPF_ALU.|BPF_NEG)        then step (s with A := uint32.(opp) s.(A))
    else if i.(code) == (BPF_MISC.|BPF_TAX)       then step (s with X := s.(A))
    else if i.(code) == (BPF_MISC.|BPF_TXA)       then step (s with A := s.(X))
    else done uint32.(zero).
  
  Fixpoint execute' {R} (instrs : list instruction) (s : state) (skip : nat) (ret : uint32 -> R) {struct instrs} : R :=
    match instrs with
    | nil => ret uint32.(zero) (* TODO: is this an invalid program? *)
    | i::instrs' =>
      match skip with
      | O =>
        execute_instruction i s
                            (fun r => ret r)
                            (fun s' => execute' instrs' s' 0 ret)
                            (fun n => execute' instrs' s n ret)
      | S skip' =>
        execute' instrs' s skip' ret
      end
    end.
  
  Definition execute instrs :=
    execute'
      instrs
      {| A := uint32.(zero); X := uint32.(zero); mem := List.repeat uint32.(zero) BPF_MEMWORDS |}
      0 id.
End with_loaders.

Notation constNone := (fun _ => None).

Import ListNotations BinInt. Local Open Scope Z_scope.
Local Notation u8 x := (exist _ x%Z eq_refl).
Local Notation u16 x := (exist _ x%Z eq_refl).
Local Notation u32 x := (exist _ x%Z eq_refl).
Section bpfcode.
  Definition bpfcode := [
    Build_instruction (u16 48) (u8 0) (u8 0) (u32 4294963204) ;
    Build_instruction (u16 21) (u8 22) (u8 0) (u32 4) ;
    Build_instruction (u16 21) (u8 21) (u8 0) (u32 3) ;
    Build_instruction (u16 128) (u8 0) (u8 0) (u32 0) ;
    Build_instruction (u16 37) (u8 19) (u8 0) (u32 2048) ;
    Build_instruction (u16 40) (u8 0) (u8 0) (u32 4294963200) ;
    Build_instruction (u16 21) (u8 12) (u8 0) (u32 34525) ;
    Build_instruction (u16 21) (u8 1) (u8 0) (u32 2048) ;
    Build_instruction (u16 5) (u8 0) (u8 0) (u32 15) ;
    Build_instruction (u16 48) (u8 0) (u8 0) (u32 9) ;
    Build_instruction (u16 21) (u8 0) (u8 13) (u32 17) ;
    Build_instruction (u16 40) (u8 0) (u8 0) (u32 6) ;
    Build_instruction (u16 69) (u8 11) (u8 0) (u32 8191) ;
    Build_instruction (u16 177) (u8 0) (u8 0) (u32 0) ;
    Build_instruction (u16 135) (u8 0) (u8 0) (u32 0) ;
    Build_instruction (u16 53) (u8 0) (u8 8) (u32 20) ;
    Build_instruction (u16 72) (u8 0) (u8 0) (u32 2) ;
    Build_instruction (u16 21) (u8 0) (u8 6) (u32 443) ;
    Build_instruction (u16 6) (u8 0) (u8 0) (u32 65535) ;
    Build_instruction (u16 48) (u8 0) (u8 0) (u32 6) ;
    Build_instruction (u16 21) (u8 0) (u8 3) (u32 17) ;
    Build_instruction (u16 40) (u8 0) (u8 0) (u32 42) ;
    Build_instruction (u16 21) (u8 0) (u8 1) (u32 443) ;
    Build_instruction (u16 6) (u8 0) (u8 0) (u32 65535) ;
    Build_instruction (u16 6) (u8 0) (u8 0) (u32 0)
  ].
End bpfcode.

Local Notation "A <- X ; B"
  := (match X with
      | Some A => B
      | None => _
      end)
       (at level 70, right associativity, format "'[v' A  <-  X ; '/' B ']'").

(* flags for partial evaluation machinery *)

Local Arguments Pos.to_nat !_.
Local Arguments Z.eqb !_ !_.
Local Arguments Z.geb !_ !_.
Local Arguments Z.gtb !_ !_.
Local Arguments Z.lor !_ !_.
Local Arguments Z.land !_ !_.
Local Arguments Z.shiftr !_ !_.
Local Arguments Z.shiftl !_ !_.
Local Arguments Z.add !_ !_.
Local Arguments Z.sub !_ !_.
Local Arguments Z.opp !_.
Local Arguments Z.mul !_ !_.
Local Arguments Z.div !_ !_.

Local Infix ".|" := Z.lor (at level 50) : Z_scope.
Local Infix ".&" := Z.land (at level 50) : Z_scope.
Local Infix "<<" := Z.shiftl (at level 50) : Z_scope.
Local Infix ">>" := Z.shiftr (at level 50) : Z_scope.

Local Notation "'uint32_t'" := ({z : Z | z mod 4294967296 = z}) : type_scope.
Local Notation "'(uint32_t)' x" := (exist (fun z : Z => z mod 4294967296 = z) x _) (at level 10).
Local Notation "0" := (exist (fun z : Z => z mod 4294967296 = z) 0 _).
Local Notation "'(ℤ)'" := proj1_sig.

(* Example of partial evaluation of bpf code to if statements *)

Goal forall P len ldb ldh ldw (xs:list instruction), P (execute len (fun x => ldb (proj1_sig x)) (fun x => ldh (proj1_sig x)) (fun x => ldw (proj1_sig x)) bpfcode).
  intros.
  Time cbn.
Abort.
