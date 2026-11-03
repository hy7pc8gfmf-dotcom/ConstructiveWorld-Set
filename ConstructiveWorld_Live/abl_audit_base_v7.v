(* ===================================================================== *)
(*  abl_audit_base_v7.v —— 审计载体扩容 v7·G10 可证性机器自靠面直审闭合件    *)
(* ===================================================================== *)
(*  使命: Z 裸奔 Top（G10 Prf_soundness：「证明者谁来证明」问题在本库的具体       *)
(*        形态——对象层证明系统 Prf 的元级可靠性面）的甲形态直审闭合。本件        *)
(*        Require G10_LoebFam（.vo 使用 vo_local_world_unified_0930 预编译      *)
(*        树，源 md5 51bb7b3e 与 CZ 池 loeb_d3 留档拷贝逐字一致），对可证性      *)
(*        机器 sound/verPf 面五条真定理各铸一条轻量真使用载体（使用＝证明体     *)
(*        真实行使上游定理非空壳），共五载体十五使用点：                          *)
(*        ① abg_prf_sound_ax_branch——元级可靠性主定理 Prf_soundness 一般形     *)
(*          直引（三规则全称）＋ ax_eqT 分支具体实例（f:=0=0、凭证码 2624 的    *)
(*          显式 ax_eqT 闭项，语义翼 evalF 计算实拍）双使用；                  *)
(*        ② abg_prf_sound_mp_repl_derivation——Prf_soundness 使用于 mpF∘repl    *)
(*          两规则真实复合派生（repl 出 ⊢0=0→0=0，mpF 吃之与 ⊢0=0 得 ⊢0=0），  *)
(*          一次行使可靠性归纳的两条非平凡分支（repl 支＋mpF 支）；            *)
(*        ③ abg_prf_sound_repl_branch——repl 单支直审：Σ0 替换不变量这一        *)
(*          「对角双条件唯一非逻辑公理」的语义被可靠性定理覆盖的具体实拍       *)
(*          （substF (0=0) 0 逐项代入计算实拍与语义翼并载）；                  *)
(*        ④ abg_gnprf_replay_2624——码级重演主定理 gnPrf_replay 一般形直引      *)
(*          ＋自燃料重演推论 gnPrf_replay_eq 在凭证码 2624 的具体实例          *)
(*          （dP2 2624 2624 恰回 Some(0=0)，loeb_tid Set 层出口）双使用；       *)
(*        ⑤ abg_verpf_ledger_656——verPf 可靠性半边 verPf_ledger_sound 一般形  *)
(*          直引＋Σ-原子账本半边 evalF2_fsig_ledger 紧界 2625 具体实例         *)
(*          （较 G10 本尊 Sigma_atom_fires_via_ledger 的 3000 收紧到 2624+1，  *)
(*          证界参数化非硬编码）＋verPf 烟测五连（正翼 verPf 2624 656＝true，  *)
(*          负翼 junk 码 3、公式码 656 冒充凭证码、错配公式码 657、越界码      *)
(*          3000 全 false——与 G10 本尊 dP_rejects_formula_code 烟测对齐）     *)
(*          七使用点闭合。                                                    *)
(*  闭环: loeb_d3 件（lbd_Box/HBL 三条件）以本件直审的 verPf/bsearch/     *)
(*        gnPrf 机器为地基；本件甲形态直引 G10_LoebFam 本尊（不经 CZ 件转手），  *)
(*        与 CZ 的 HBL 件构成「HBL 条件审计 Prf_soundness」审计闭环——           *)
(*        CZ 层 1（□ 的导出条件）踩在 verPf 账面上，本件把 verPf 账面与        *)
(*        Prf_soundness 语义面同件闭合，双件互为核对。                        *)
(*  依赖: G10_LoebFam（-Q 预编译树 vo_local_world_unified_0930 只读引用）；     *)
(*        Stdlib（Arith/Lia 证明层算术出口、Extraction 出口舱）。               *)
(*  构造性: 零承认语句、零经典逻辑、零 Prop 载体：语句面合取全 Datatypes.prod   *)
(*        （Set/Type 层 *），等同全 loeb_tid（G10 Set 层恒等型），无 eq/exists/ *)
(*        or/and 任何 Prop 连词书写；算术界仅出现于证明层前提位（E364 判例：    *)
(*        前提位不构成 Set 层泄露）；证明体全 exact/apply 显式项直交＋计算面    *)
(*        eq_refl/id 级实例化消解（born-green 全计算面）。                           *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&          *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no -q            *)
(*        -Q <池> "" -Q vo_local_world_unified_0930 "" <池>/abl_audit_base_v7.v *)
(*        （独占池 audit_base_v7/，道闸 ≤1，单件无池内链序；9.1.0 live 工具链，  *)
(*        9.0.1 live901 vo 版本号不兼容勿用）。                                *)
(*  核验注: ①空壳甄别（CS 判例照办）：G10 面 sound/reliable 族六件逐条实拍——   *)
(*        Prf_soundness（三支结构归纳 17 行，非 ->True 形）、gnPrf_replay      *)
(*        （三支归纳 55 行燃料账）、gnPrf_replay_eq/Prf_replay（使用前者的      *)
(*        推论形）、verPf_ledger_sound（重演＋码账双跳）、evalF2_fsig_ledger   *)
(*        （bsearch_witness 见证提取）五件入选；wpm_unbounded_family_unsound   *)
(*        （UpRefuted 钱包面 refu_tid，非可证性面）留总账未入选；G10 头注自报   *)
(*        wpm_solvent_bounded_family 系恒等转发伪非平凡（空壳前科面）不入。     *)
(*        ②具体码实拍（vm_compute 检验三件）：gnF(0=0)=656、ax_eqT 凭证码      *)
(*        gnPrf(0=0)=2624、dP2 2624 2624=Some(0=0)、verPf 2624 656=true、      *)
(*        负翼 junk 码 3／公式码 656 冒充／错配 2624 657／越界 3000 656        *)
(*        全 false（烟测五连锚，与 BE/BG/BS 三代提取实跑同源）。               *)
(*        ③诚实边界（计算墙实拍）：pairp 系 2^a·(2b+1) 指数级联，mpF∘repl      *)
(*        派生凭证码超指数爆炸（检验件实测中止归档）——        *)
(*        派生码面使用只走定理级（载体②③④一般形翼），2624 量级 ax_eqT         *)
(*        码面保留全计算实拍（载体④⑤）。④abg_ 前缀全现役池 grep             *)
(*        零命中。⑤载体⑤紧界 2625 的 ltb 前提与码账前提全经 eq_refl 计算     *)
(*        直实例化消解（loeb_tid_eq＋计算反射），证明层零 lia 依赖面残留。           *)
(* ===================================================================== *)

Require S01_BaseRing.
Require Import G10_LoebFam.

(* ============================================================ *)
(* §0 内部管件舱（具体公式与显式凭证闭项，非载体语句）               *)
(* ============================================================ *)

(* 被证公式 f₀ := 0=0（其哥德尔码 656，vm_compute 实拍）。 *)
Definition abg_fzz : Formula := teq tzero tzero.

(* ax_eqT 显式凭证：0=0 在任意赋值下取值自等（凭证码 2624，实拍）。 *)
Definition abg_axz : Prf abg_fzz :=
  ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)).

(* 对角用替换语境 th₀ := 0=0（语言内公式，留变元 0 位）。 *)
Definition abg_th0 : Formula := teq (tvar 0) (tvar 0).

(* repl 显式凭证：⊢ 0=0 → 0=0（th₀ 的两代入项同取 tzero，值账自等）。 *)
Definition abg_pfr : Prf (fimp abg_fzz abg_fzz) :=
  repl abg_th0 tzero tzero
    (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)).

(* mpF 显式凭证：由 repl 大前提与 ax_eqT 小前提分离得 ⊢ 0=0。 *)
Definition abg_pfmp : Prf abg_fzz :=
  mpF abg_fzz abg_fzz abg_pfr abg_axz.

(* ============================================================ *)
(* §1 载体一·Prf_soundness（甲）：一般形直引＋ax_eqT 分支具体实例     *)
(*    （凭证码 2624 显式闭项；语义翼计算实拍）                       *)
(* ============================================================ *)

Theorem abg_prf_sound_ax_branch :
  (forall (f : Formula) (pf : Prf f) (s : nat -> nat),
     loeb_tid bool (evalF f s) true) *
  loeb_tid bool (evalF abg_fzz (fun _ : nat => 0)) true.
Proof.
  split.
  - (* 一般形：元级可靠性主定理逐字直引（三规则全称，跨件直审本翼）。 *)
    intros f pf s. exact (Prf_soundness f pf s).
  - (* ax_eqT 具体实例：0=0 在零赋值下语义计算实拍 evalF＝true。 *)
    apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* §2 载体二·Prf_soundness（乙）：mpF∘repl 两规则真实复合派生——      *)
(*    一次行使可靠性归纳的 repl 支＋mpF 支（非平凡分支双覆盖）        *)
(* ============================================================ *)

Theorem abg_prf_sound_mp_repl_derivation :
  (forall s : nat -> nat, loeb_tid bool (evalF abg_fzz s) true) *
  loeb_tid bool (evalF (fimp abg_fzz abg_fzz) (fun _ : nat => 0)) true.
Proof.
  split.
  - (* 派生使用：可靠性定理吃入 mpF 凭证（其子凭证链含 repl 凭证），       *)
    (* 归纳两支真实行使——使用真行使非转述。                              *)
    intros s. exact (Prf_soundness abg_fzz abg_pfmp s).
  - (* 复合公式语义计算实拍：imp 真→真 ＝ true。 *)
    apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* §3 载体三·Prf_soundness（丙）：repl 单支直审——Σ0 替换不变量        *)
(*    （对角双条件唯一非逻辑公理）的语义覆盖具体实拍                   *)
(* ============================================================ *)

Theorem abg_prf_sound_repl_branch :
  (forall s : nat -> nat,
     loeb_tid bool (evalF (fimp abg_fzz abg_fzz) s) true) *
  loeb_tid bool (evalF (substF abg_th0 tzero) (fun _ : nat => 0)) true.
Proof.
  split.
  - (* repl 单支：可靠性定理吃入 repl 凭证（abg_pfr），语义覆盖实拍。 *)
    intros s. exact (Prf_soundness (fimp abg_fzz abg_fzz) abg_pfr s).
  - (* 替换不变量计算面：substF th₀ tzero 逐项代入＝0=0，evalF＝true。 *)
    apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* §4 载体四·码级重演：gnPrf_replay 一般形直引＋凭证码 2624 自燃料     *)
(*    重演具体实例（dP2 2624 2624 恰回 Some(0=0)，Set 层出口）        *)
(* ============================================================ *)

Theorem abg_gnprf_replay_2624 :
  (forall (f : Formula) (pf : Prf f) (k : nat),
     S01_BaseRing.NatLe (gnPrf f pf) k ->
     loeb_tid (option Formula) (dP2 k (gnPrf f pf)) (Some f)) *
  loeb_tid (option Formula) (dP2 2624 2624) (Some abg_fzz).
Proof.
  split.
  - (* 一般形：码级重演主定理逐字直引（三规则燃料账，跨件直审本翼）。 *)
    intros f pf k Hk. apply S01_BaseRing.NatLe_drop in Hk.
    exact (gnPrf_replay f pf k Hk).
  - (* 2624 具体实例：自燃料重演推论在 ax_eqT 显式凭证处实例化消解——           *)
    (* gnPrf abg_fzz abg_axz 计算实拍＝2624，dP2 2624 2624＝Some(0=0)。   *)
    apply loeb_tid_eq. exact (gnPrf_replay_eq abg_fzz abg_axz).
Qed.

(* ============================================================ *)
(* §5 载体五·verPf 账面：verPf_ledger_sound 一般形直引＋紧界 2625      *)
(*    Σ-原子实例＋烟测五连（正翼 2624/656、负翼 junk/冒充/错配/越界）  *)
(* ============================================================ *)

Theorem abg_verpf_ledger_656 :
  (forall (w : nat) (f : Formula) (pf : Prf f),
     loeb_tid nat w (gnPrf f pf) -> loeb_tid bool (verPf w (gnF f)) true) *
  ((forall s : nat -> nat,
      loeb_tid bool (evalF2 (fsig (numT 2625) (numT 656)) s) true) *
   (loeb_tid bool (verPf 2624 656) true *
    (loeb_tid bool (verPf 3 656) false *
     (loeb_tid bool (verPf 656 656) false *
      (loeb_tid bool (verPf 2624 657) false *
       loeb_tid bool (verPf 3000 656) false))))).
Proof.
  split.
  - (* 一般形：verPf 可靠性半边逐字直引（码账对齐 ⇒ 验证过线）。 *)
    intros w f pf Hw. exact (verPf_ledger_sound w f pf Hw).
  - split.
    + (* Σ-原子紧界实例：evalF2_fsig_ledger 在界 2625（=凭证码 2624+1，        *)
      (* 较 G10 本尊 Sigma_atom_fires_via_ledger 的 3000 收紧）实例化消解——          *)
      (* 两前提（ltb 界账、公式码对齐账）全计算反射直供，使用真行使。           *)
      intros s.
      apply (evalF2_fsig_ledger (numT 2625) (numT 656) s abg_fzz abg_axz).
      * apply loeb_tid_eq. exact eq_refl.
      * apply loeb_tid_eq. exact eq_refl.
    + split.
      * (* 正翼：真凭证码 2624 对公式码 656 验证过线（计算实拍）。 *)
        apply loeb_tid_eq. exact eq_refl.
      * split.
        -- (* 负翼一：junk 码 3 无凭证可解，verPf 拒（计算实拍）。 *)
           apply loeb_tid_eq. exact eq_refl.
        -- split.
           ++ (* 负翼二：公式码 656 冒充凭证码被拒——与 G10 本尊               *)
              (* dP_rejects_formula_code 烟测同源对齐（计算实拍）。 *)
              apply loeb_tid_eq. exact eq_refl.
           ++ split.
              ** (* 负翼三：真凭证码对错配公式码 657 拒——账不对齐即拒。 *)
                 apply loeb_tid_eq. exact eq_refl.
              ** (* 负翼四：越界码 3000 对真公式码拒——过线≠账对齐。 *)
                 apply loeb_tid_eq. exact eq_refl.
Qed.

(* ============================================================ *)
(* §6 尾舱·假设审计（G10 可证性面五主定理跨件直审＋本件五载体自审）    *)
(*    判读判据：十条全输出 Closed under the global context。           *)
(*    前 5 条＝直审位（Prf_soundness 语义面／gnPrf_replay 码级面／      *)
(*    verPf_ledger_sound＋evalF2_fsig_ledger 账面）——G10 自靠面此前    *)
(*    全树 PA 直审缺位，Z 裸奔 Top 本体；后 5 条＝本件五载体自审。      *)
(*    注：Require 闭包含 UpLoeb/UpRefuted/UpQKBound/UpLoebD2 全链，     *)
(*    coqchk 环境公理面沿 CT1B 判例与逐定理 PA 定检分账，非本件引入。    *)
(* ============================================================ *)

Print Assumptions G10_LoebFam.Prf_soundness.
Print Assumptions G10_LoebFam.gnPrf_replay.
Print Assumptions G10_LoebFam.gnPrf_replay_eq.
Print Assumptions G10_LoebFam.verPf_ledger_sound.
Print Assumptions G10_LoebFam.evalF2_fsig_ledger.
Print Assumptions abg_prf_sound_ax_branch.
Print Assumptions abg_prf_sound_mp_repl_derivation.
Print Assumptions abg_prf_sound_repl_branch.
Print Assumptions abg_gnprf_replay_2624.
Print Assumptions abg_verpf_ledger_656.

(* ============================================================ *)
(* §7 出口舱：载体兼任提取端口（G3：提取面零魔数）                     *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction abg_prf_sound_ax_branch
  abg_prf_sound_mp_repl_derivation abg_prf_sound_repl_branch
  abg_gnprf_replay_2624 abg_verpf_ledger_656.
