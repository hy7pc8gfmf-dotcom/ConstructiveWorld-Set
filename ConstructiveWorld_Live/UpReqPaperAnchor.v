(* ====================================================================== *)
(*  UpReqPaperAnchor.v -- paper-citation stable anchor mechanism (A1)      *)
(*  Mission. Paper citations of library coordinates (file:line) drift on   *)
(*    every mass-replacement wave (six waves measured; live sample: the    *)
(*    paper-7 citation of mtw_window_two_sided at L172-186, now L187).     *)
(*    This file moves paper citations from line numbers to stable anchor   *)
(*    symbols: named anchor records live here, papers cite the symbol, and *)
(*    the symbol tracks the moving implementation without breaking.        *)
(*    Mechanics: authoritative locating = theorem-name primary key (decl   *)
(*    line, word-boundary unique; line number = snapshot only; nameless    *)
(*    conclusion blocks use a unique content-phrase key, first instance    *)
(*    eps_split; file-level anchors use reserved key FILE_LEVEL); record = *)
(*    (file, key, line snapshot, baseline md5, self-check day, paper       *)
(*    domain); zero Require, never touches the anchored layer, refresh     *)
(*    moves only the snapshot triple, symbol names never change.           *)
(*  Dependencies. Stdlib Ascii and String only; zero tree-library Require. *)
(*    Set-layer statement carriers are realized in-file (Id 1:1 with the   *)
(*    S-tree base face; And := prod, the Set product), embeddable in any   *)
(*    target pool.                                                         *)
(*  References. Baseline module UpReqPaperAnchor.v of ConstructiveWorld_   *)
(*    Live (statement faces 1:1; machine census 30 = 30); coordinate, md5  *)
(*    and day fields are measured snapshots of anchor-establishment day;   *)
(*    a trailing ? marks attribution still unverified, not claimed.        *)
(*  Constructivity. No assumption-introducing command anywhere; every      *)
(*    proof ends in Qed; statements ride Set carriers (Id/And); no         *)
(*    classical logic; Print Assumptions audit at file end; the extraction *)
(*    probe reports Obj.magic = 0 on both faces.                           *)
(*  Build. rocq c -native-compiler no -q -Q . "" UpReqPaperAnchor.v        *)
(*    (Rocq 9.1 toolchain; single -Q root with an empty logical prefix).   *)
(* ====================================================================== *)

From Stdlib Require Import Ascii String.

(* ---------- Set-layer statement carriers (in-file, zero-tree) ---------- *)
(* The statement face of every machine-check invariant below is carried on *)
(* Set: equality faces ride Id and conjunction faces ride the Set product. *)
(* Id is the S-tree base identity type, copied 1:1; And is definitionally  *)
(* the Set product (the S-tree base declares it as And A B : Set := A*B;   *)
(* here the same term is reached through a plain alias, which keeps the    *)
(* top-level statement census identical with the source file).             *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Notation And := prod.

(* ---------- Anchor record type ---------- *)

Record PaperAnchor : Set := MkPaperAnchor
  { pan_file   : string   (* anchored file name (.v) *)
  ; pan_symbol : string   (* primary key: theorem-name decl level / unique
                             content-phrase level / FILE_LEVEL *)
  ; pan_line   : nat      (* auxiliary line-number snapshot (current at
                             anchor-establishment day, drifts, auxiliary only) *)
  ; pan_md5    : string   (* anchored-file baseline md5 (whole-file digest of
                             anchor-establishment day) *)
  ; pan_day    : nat      (* self-check day yyyymmdd *)
  ; pan_paper  : string   (* citing paper domain (domain level; a trailing ?
                             marks precise attribution still to verify) *)
  }.

(* ---------- Machine-check tool face ---------- *)

Definition pan_b (b : bool) : nat := if b then 1 else 0.

Definition pan_ck (c : ascii) : nat :=
  match c with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7 =>
      pan_b a0 + 2 * pan_b a1 + 4 * pan_b a2 + 8 * pan_b a3
      + 16 * pan_b a4 + 32 * pan_b a5 + 64 * pan_b a6 + 128 * pan_b a7
  end.

Fixpoint pan_sck (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => pan_ck c + pan_sck s'
  end.

Fixpoint pan_slen (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ s' => S (pan_slen s')
  end.

Fixpoint pan_len (l : list PaperAnchor) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (pan_len tl)
  end.

Fixpoint pan_seqb (s t : string) : bool :=
  match s, t with
  | EmptyString, EmptyString => true
  | String c s', String d t' => if ascii_dec c d then pan_seqb s' t' else false
  | _, _ => false
  end.

Fixpoint pan_find (k : string) (l : list PaperAnchor) : option PaperAnchor :=
  match l with
  | nil => None
  | cons a tl => if pan_seqb k (pan_symbol a) then Some a else pan_find k tl
  end.

(* ---------- First batch of 8 anchors ---------- *)

(* Paper-1/2 second-law face: SecondLawQuantified.v, two anchors (P1/P2
   domain) *)
Definition pan_slq_entropy_gain_kl_lower : PaperAnchor :=
  MkPaperAnchor "SecondLawQuantified.v" "slq_entropy_gain_kl_lower" 243
    "f00e7b8fbbe4feba99818bbe7ba841eb" 20260922 "P1/P2".

Definition pan_slq_second_law_eps_list : PaperAnchor :=
  MkPaperAnchor "SecondLawQuantified.v" "slq_second_law_eps_list" 498
    "f00e7b8fbbe4feba99818bbe7ba841eb" 20260922 "P1/P2".

(* Engine ceiling cec_trunc_sup: REIN A1 first batch; precise paper
   attribution to verify *)
Definition pan_cec_trunc_sup : PaperAnchor :=
  MkPaperAnchor "UpReqEngineCeiling.v" "cec_trunc_sup" 275
    "1095c5835c4ef1a563dafbcbb33b75c8" 20260922 "P1/P2?".

(* Paper-5 domain: UpReqPinskerCore.v epsilon-trichotomy conclusion (a
   nameless block, unique content-phrase primary key; current L24; precise
   paper attribution to verify) *)
Definition pan_pnk_eps_trichotomy : PaperAnchor :=
  MkPaperAnchor "UpReqPinskerCore.v" "eps_split" 24
    "f616d4b7ed858041729198b63d1021b9" 20260922 "P5?".

(* Paper-4: SqrtfCauchyArch.v, one of the five ablation anchors (REIN A9
   face) *)
Definition pan_sfcy_arch_decay_slot : PaperAnchor :=
  MkPaperAnchor "SqrtfCauchyArch.v" "sfcy_arch_decay_slot" 446
    "d1ffe23723b7f6506e6a047ebfee6172" 20260922 "P4".

(* Paper-7: UpAblMetaWindow.v window theorem -- a living drift specimen
   (the paper cites L172-186, current L187) *)
Definition pan_mtw_window_two_sided : PaperAnchor :=
  MkPaperAnchor "UpAblMetaWindow.v" "mtw_window_two_sided" 187
    "ffa0c2662e6d8bc91db45fc6882c3627" 20260922 "P7".

(* Paper-7: UpReqUMixSelect.v -- the ums_k_select anchor (declaration line
   measured at L532) *)
Definition pan_ums_k_select : PaperAnchor :=
  MkPaperAnchor "UpReqUMixSelect.v" "ums_k_select" 532
    "cbf1aba4caaa77dd68789a55f5316502" 20260922 "P7".

(* Paper-6/7: UpReqConcFin2.v file-level anchor (reserved primary key
   FILE_LEVEL, whole file at 1644 lines currently) *)
Definition pan_upreq_concfin2_file : PaperAnchor :=
  MkPaperAnchor "UpReqConcFin2.v" "FILE_LEVEL" 1644
    "852d27ee570b086e20b91f6841da339d" 20260922 "P6/P7".

(* ---------- Anchor list (adding an entry = one more cons at the tail,
   append-only) ---------- *)

Definition pan_anchor_list : list PaperAnchor :=
  pan_slq_entropy_gain_kl_lower :: pan_slq_second_law_eps_list ::
  pan_cec_trunc_sup :: pan_pnk_eps_trichotomy :: pan_sfcy_arch_decay_slot ::
  pan_mtw_window_two_sided :: pan_ums_k_select :: pan_upreq_concfin2_file :: nil.

(* ---------- Machine-check invariant face ---------- *)
(* Every invariant below is carried on Set: each component equality rides  *)
(* Id, the eight-component conjunction rides the Set product.  A renamed   *)
(* anchor key or a tampered string turns the compile red (anti-tamper      *)
(* face); every proof closes by the Id constructor after conversion.       *)

(* Primary-key content checksums: renaming an anchor key or mistyping the
   string breaks the compile (anti-tamper face) *)
Lemma pan_sym_ck_invariant :
  And (Id (pan_sck (pan_symbol pan_slq_entropy_gain_kl_lower)) 2684)
      (And (Id (pan_sck (pan_symbol pan_slq_second_law_eps_list)) 2448)
      (And (Id (pan_sck (pan_symbol pan_cec_trunc_sup)) 1389)
      (And (Id (pan_sck (pan_symbol pan_pnk_eps_trichotomy)) 979)
      (And (Id (pan_sck (pan_symbol pan_sfcy_arch_decay_slot)) 2104)
      (And (Id (pan_sck (pan_symbol pan_mtw_window_two_sided)) 2160)
      (And (Id (pan_sck (pan_symbol pan_ums_k_select)) 1278)
           (Id (pan_sck (pan_symbol pan_upreq_concfin2_file)) 759))))))).
Proof. repeat split; apply id_refl. Qed.

(* Anchored-file-name content checksums *)
Lemma pan_file_ck_invariant :
  And (Id (pan_sck (pan_file pan_slq_entropy_gain_kl_lower)) 2094)
      (And (Id (pan_sck (pan_file pan_slq_second_law_eps_list)) 2094)
      (And (Id (pan_sck (pan_file pan_cec_trunc_sup)) 1954)
      (And (Id (pan_sck (pan_file pan_pnk_eps_trichotomy)) 1782)
      (And (Id (pan_sck (pan_file pan_sfcy_arch_decay_slot)) 1679)
      (And (Id (pan_sck (pan_file pan_mtw_window_two_sided)) 1655)
      (And (Id (pan_sck (pan_file pan_ums_k_select)) 1652)
           (Id (pan_sck (pan_file pan_upreq_concfin2_file)) 1379))))))).
Proof. repeat split; apply id_refl. Qed.

(* md5-field 32-character well-formedness invariant *)
Lemma pan_md5_len_invariant :
  And (Id (pan_slen (pan_md5 pan_slq_entropy_gain_kl_lower)) 32)
      (And (Id (pan_slen (pan_md5 pan_slq_second_law_eps_list)) 32)
      (And (Id (pan_slen (pan_md5 pan_cec_trunc_sup)) 32)
      (And (Id (pan_slen (pan_md5 pan_pnk_eps_trichotomy)) 32)
      (And (Id (pan_slen (pan_md5 pan_sfcy_arch_decay_slot)) 32)
      (And (Id (pan_slen (pan_md5 pan_mtw_window_two_sided)) 32)
      (And (Id (pan_slen (pan_md5 pan_ums_k_select)) 32)
           (Id (pan_slen (pan_md5 pan_upreq_concfin2_file)) 32))))))).
Proof. repeat split; apply id_refl. Qed.

(* Uniform self-check-day invariant: a refresh must turn the whole column
   (a mechanical reminder); a single stale anchor is disallowed *)
Lemma pan_day_uniform_invariant :
  And (Id (pan_day pan_slq_entropy_gain_kl_lower) 20260922)
      (And (Id (pan_day pan_slq_second_law_eps_list) 20260922)
      (And (Id (pan_day pan_cec_trunc_sup) 20260922)
      (And (Id (pan_day pan_pnk_eps_trichotomy) 20260922)
      (And (Id (pan_day pan_sfcy_arch_decay_slot) 20260922)
      (And (Id (pan_day pan_mtw_window_two_sided) 20260922)
      (And (Id (pan_day pan_ums_k_select) 20260922)
           (Id (pan_day pan_upreq_concfin2_file) 20260922))))))).
Proof. repeat split; apply id_refl. Qed.

(* Anchor-list count closure *)
Lemma pan_anchor_list_len : Id (pan_len pan_anchor_list) 8.
Proof. apply id_refl. Qed.

(* ---------- Resolution face: in-file machine check of the paper-side
   "primary key -> anchor record" lookup ---------- *)

Lemma pan_find_slq_entropy_gain_kl_lower :
  Id (pan_find "slq_entropy_gain_kl_lower" pan_anchor_list)
     (Some pan_slq_entropy_gain_kl_lower).
Proof. apply id_refl. Qed.

Lemma pan_find_slq_second_law_eps_list :
  Id (pan_find "slq_second_law_eps_list" pan_anchor_list)
     (Some pan_slq_second_law_eps_list).
Proof. apply id_refl. Qed.

Lemma pan_find_cec_trunc_sup :
  Id (pan_find "cec_trunc_sup" pan_anchor_list) (Some pan_cec_trunc_sup).
Proof. apply id_refl. Qed.

Lemma pan_find_pnk_eps_trichotomy :
  Id (pan_find "eps_split" pan_anchor_list) (Some pan_pnk_eps_trichotomy).
Proof. apply id_refl. Qed.

Lemma pan_find_sfcy_arch_decay_slot :
  Id (pan_find "sfcy_arch_decay_slot" pan_anchor_list)
     (Some pan_sfcy_arch_decay_slot).
Proof. apply id_refl. Qed.

Lemma pan_find_mtw_window_two_sided :
  Id (pan_find "mtw_window_two_sided" pan_anchor_list)
     (Some pan_mtw_window_two_sided).
Proof. apply id_refl. Qed.

Lemma pan_find_ums_k_select :
  Id (pan_find "ums_k_select" pan_anchor_list) (Some pan_ums_k_select).
Proof. apply id_refl. Qed.

Lemma pan_find_upreq_concfin2_file :
  Id (pan_find "FILE_LEVEL" pan_anchor_list) (Some pan_upreq_concfin2_file).
Proof. apply id_refl. Qed.

(* Suffix-family confusion, mechanically excluded: an unregistered suffix
   name resolves to None (lesson of ums_k_select vs ums_k_select_le -- the
   primary-key uniqueness criterion must carry a word boundary; this face
   machine-checks that semantics in-file) *)
Lemma pan_find_suffix_family_miss :
  Id (pan_find "ums_k_select_le" pan_anchor_list) None.
Proof. apply id_refl. Qed.

(* ---------- Assumption audit ---------- *)
(* Each Print Assumptions below reports "Closed under the global context"  *)
(* (zero external unproven assumptions).                                   *)

Print Assumptions pan_anchor_list.
Print Assumptions pan_find.
Print Assumptions pan_sym_ck_invariant.
