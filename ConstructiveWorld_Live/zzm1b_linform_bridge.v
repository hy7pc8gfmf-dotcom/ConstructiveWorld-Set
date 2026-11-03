(* ===================================================================== *)
(*  zzm1b_linform_bridge.v —— Q(i) 残数算术组机·层 2 围道离散化桥（DM-ZZM1·切片 1） *)
(*  模块名：zzm1b_linform_bridge。单源生成器：ZZ/_log/_zzm_anchor_gen.py       *)
(*         （对照 _mirror_zz.py MIRROR_GREEN 10/10 在卷后独立复算·S1a/S1b/S2/  *)
(*          S4 四判据一致后单源发射本件——供件同源·禁手改数值字面量）。          *)
(*  使命（ZZ2 设计单层 2·半机起步首铸层间桥）：线性形式的端点算术定义——        *)
(*        有限和离散化（多项式部贡献 + 主部 j≥1 贡献 + s 通道），层 1 残数      *)
(*        （zzm1_gauss 的 gz/gz_pow/gnorm 除法自由形）→层 3 读出的层间桥。        *)
(*        桥=定义（非积分算子·设计单核心发现：端点算术使离散化层无独立语句面    *)
(*        义务）；构造性注记：零 Axiom·零 Prop 语句·全部语句 Set 承载（zzId/zid 形）。       *)
(*  锚面（n=1..6 数值锚经新机件复算全一致·三路对照先行律）：                    *)
(*        ①端点幂表一致×3：gz_pow 复算 vs 本生成器独立值（−1+2i)^k k=1..23、    *)
(*          gz_im_neg_frac 除法自由对 (4+2i)/(6+2i) j=1..18（红笔③ norm 档     *)
(*          20/40 即此层锚）；②族锚×n：Pq/A/B 系数表字面量入桥 → r_n/s_n        *)
(*          vm_compute 一致（对照认证域 certified 值）；③对称锚 A_j=B_j 全表；  *)
(*          ④非零性核心 Z 证书（层 2④缺口机形替代的算术核）；⑤sigT 正典承载    *)
(*          zz_linform_sig（层 3 读出接口位·切片 4 使用）。                      *)
(*  忠实性披露（律五）：zz_linform_r/s = REALFORM I_n/(2i) 的 Q 读出属复分析面   *)
(*        （围道积分↔端点算术·库无 Cauchy 基座）——对照 float 围道 Simpson ↔     *)
(*        Fractions 精确一致 8.5e−16（n=1..6）＝对照域认证在卷，非 Coq 义务；    *)
(*        系数表上游（pdivmod/pshift/Laurent 提取）＝设计单五件之 3/4 件＝切片   *)
(*        2-3 候·本片以对照认证域 certified 系数表字面量为供件（同源登记）。     *)
(*  依赖：Stdlib QArith/ZArith/List＋池内 zzm1_gauss（ZZM-1）。零外部证书器、    *)
(*        零实数层、零经典逻辑、Obj.magic=0。                                   *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&           *)
(*        ulimit -s 65532 && cd 本池 && bash cpu_guard.sh -- rocq c             *)
(*        -native-compiler no -q -Q _world "" zzm1b_linform_bridge.v            *)
(*        （前置：zzm1_gauss.vo 已入 _world）。                                 *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith List.
Import ListNotations.
Require Import zzm1_gauss.

Open Scope Q_scope.


(* ============================================================ *)
(* §1 层 2 桥定义（全部透明 Defined·端点算术有限和）                              *)
(* ============================================================ *)

(* 索引有限和：Σ_{k<n} f k *)
Fixpoint zz_sumf (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (zz_sumf f k + f k)%Q
  end.

(* 多项式部贡献：phat = Σ_k Pq_k·Im[(−1+2i)^{k+1}]/(k+1)
   （∫x^k 端点差＝高斯幂虚部/(k+1)·对照 gpow(−1,2,k+1) 直译）。 *)
Definition zz_phat (p : list Q) : Q :=
  zz_sumf (fun k => (nth k p 0%Q * ((gim (gz_pow (mkz (Z.opp 1) 2) (S k)) # 1)%Q)
                        / (Z.of_nat (S k) # 1)%Q)%Q) (length p).

(* 主部 j≥1 贡献：Σ_{j=1..m} −cs_j·Im[e^{−j}]/j＝Σ −cs_j·(gz_im_neg_frac 读出)/j
   （对照式 r_n -= cs_j·im_neg_power/j 同式：Im[e^{−j}] = −Im[e^j]/norm^j，
     红笔⑤ /2j 口径；norm 档 20/40＝红笔③教训锚。
     〔切片 1 红笔①：首铸此处符号结构反置（直加 imn 项），bite_r_1 vm_compute
     false fail-loud 拦截后按对照式补负号——假件拦截闸兑现记录。〕） *)
Definition zz_princ (cs : list Q) (e : gz) (m : nat) : Q :=
  zz_sumf (fun jj => match jj with
                     | O => 0%Q
                     | S j => (nth (S j) cs 0%Q
                              * (((Z.opp (fst (gz_im_neg_frac e (S j)))) # 1)
                                 / ((snd (gz_im_neg_frac e (S j))) # 1))%Q
                              / (Z.of_nat (S j) # 1)%Q)%Q
                     end) (S m).

(* 层 2 桥本体：r 通道（多项式部＋双主部）·s 通道（残位和 /8·红笔④口径） *)
Definition zz_linform_r (p As Bs : list Q) (m : nat) : Q :=
  (zz_phat p + zz_princ As (mkz 4 2) m + zz_princ Bs (mkz 6 2) m)%Q.
Definition zz_linform_s (As Bs : list Q) : Q :=
  ((nth 0 As 0%Q + nth 0 Bs 0%Q) / 8)%Q.

(* 层 1 残数项承载（部分分式各项在端点的除法自由残数）：系数 Q·端点 gz·阶 nat *)
Record zz_res : Set := MkZZRes { zz_rc : Q ; zz_re : gz ; zz_rj : nat }.
Definition zz_res_frac (t : zz_res) : Z * Z := gz_im_neg_frac (zz_re t) (zz_rj t).
Definition zz_res_q (t : zz_res) : Q :=
  ((fst (zz_res_frac t) # 1) / (snd (zz_res_frac t) # 1))%Q.

(* 表对称布尔件（A_j=B_j 全表锚用） *)
Fixpoint zz_lqeqb (l t : list Q) : bool :=
  match l, t with
  | nil, nil => true
  | x :: l', y :: t' => andb (Qeq_bool x y) (zz_lqeqb l' t')
  | _, _ => false
  end.

(* Z 对表布尔件（端点幂表锚用） *)
Fixpoint zz_plist_eqb (l t : list (Z * Z)) : bool :=
  match l, t with
  | nil, nil => true
  | (x, y) :: l', (u, v) :: t' =>
      andb (Z.eqb x u) (andb (Z.eqb y v) (zz_plist_eqb l' t'))
  | _, _ => false
  end.

(* sigT 正典承载（层 3 读出接口位·Set 层）：存在 r,s∈Q 使桥输出=⟨r,s⟩ *)
Definition zz_linform_sig (p As Bs : list Q) (m : nat) : Set :=
  sigT (fun r : Q => sigT (fun s : Q =>
    (zzId (Qeq_bool (zz_linform_r p As Bs m) r) true
     * zzId (Qeq_bool (zz_linform_s As Bs) s) true)%type)).

Lemma zz_linform_sig_inst : forall (p As Bs : list Q) (m : nat),
  zz_linform_sig p As Bs m.
Proof.
  intros p As Bs m.
  exists (zz_linform_r p As Bs m), (zz_linform_s As Bs).
  split; apply zzId_Qeqb_refl.
Qed.


(* ============================================================ *)
(* §2 端点幂表锚（层 1 机件复算 vs 生成器独立值·除法自由形直咬）                  *)
(* ============================================================ *)

Definition zz_ep_m1_ref : list (Z * Z) := [ (-1, 2)%Z; (-3, -4)%Z; (11, -2)%Z; (-7, 24)%Z; (-41, -38)%Z; (117, -44)%Z; (-29, 278)%Z; (-527, -336)%Z; (1199, -718)%Z; (237, 3116)%Z; (-6469, -2642)%Z; (11753, -10296)%Z; (8839, 33802)%Z; (-76443, -16124)%Z; (108691, -136762)%Z; (164833, 354144)%Z; (-873121, -24478)%Z; (922077, -1721764)%Z; (2521451, 3565918)%Z; (-9653287, 1476984)%Z; (6699319, -20783558)%Z; (34867797, 34182196)%Z; (-103232189, 35553398)%Z ].
Definition zz_ep_if4_ref : list (Z * Z) := [ (-2, 20)%Z; (-16, 400)%Z; (-88, 8000)%Z; (-384, 160000)%Z; (-1312, 3200000)%Z; (-2816, 64000000)%Z; (3712, 1280000000)%Z; (86016, 25600000000)%Z; (613888, 512000000000)%Z; (3190784, 10240000000000)%Z; (13248512, 204800000000000)%Z; (42172416, 4096000000000000)%Z; (72409088, 81920000000000000)%Z; (-264175616, 1638400000000000000)%Z; (-3561586688, 32768000000000000000)%Z; (-23209181184, 655360000000000000000)%Z; (-114441715712, 13107200000000000000000)%Z; (-451350102016, 262144000000000000000000)%Z ].
Definition zz_ep_if6_ref : list (Z * Z) := [ (-2, 40)%Z; (-24, 1600)%Z; (-208, 64000)%Z; (-1536, 2560000)%Z; (-10112, 102400000)%Z; (-59904, 4096000000)%Z; (-314368, 163840000000)%Z; (-1376256, 6553600000000)%Z; (-3940352, 262144000000000)%Z; (7766016, 10485760000000000)%Z; (250806272, 419430400000000000)%Z; (2699034624, 16777216000000000000)%Z; (22356164608, 671088640000000000000)%Z; (160312590336, 26843545600000000000000)%Z; (1029504499712, 1073741824000000000000000)%Z; (5941550383104, 42949672960000000000000000)%Z; (30118424608768, 1717986918400000000000000000)%Z; (123759079981056, 68719476736000000000000000000)%Z ].

Lemma zz_tab_ep_m1 : zzId (zz_plist_eqb (map (fun k => (gre (gz_pow (mkz (Z.opp 1) 2) k),
                                                     gim (gz_pow (mkz (Z.opp 1) 2) k)))
                                            (seq 1 23)) zz_ep_m1_ref) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_tab_ep_if4 : zzId (zz_plist_eqb (map (fun j => gz_im_neg_frac (mkz 4 2) j)
                                             (seq 1 18)) zz_ep_if4_ref) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_tab_ep_if6 : zzId (zz_plist_eqb (map (fun j => gz_im_neg_frac (mkz 6 2) j)
                                             (seq 1 18)) zz_ep_if6_ref) true.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* §3 族锚（n=1..6 数值锚经新机件复算全一致·对照认证域供件字面量）                *)
(* ============================================================ *)

(* ---- n=1：m=3·Pq 度 2·对照认证域系数表（极点序） ---- *)
Definition zz_pq_1 : list Q := [(560#1)%Q; (0#1)%Q; (5#1)%Q].
Definition zz_as_1 : list Q := [(-2392#1)%Q; (6880#1)%Q; (-11200#1)%Q; (8000#1)%Q].
Definition zz_bs_1 : list Q := [(-2392#1)%Q; (6880#1)%Q; (-11200#1)%Q; (8000#1)%Q].
Definition zz_r_1 : Q := (5636#3)%Q.
Definition zz_s_1 : Q := (-598#1)%Q.

Lemma zz_bite_r_1 : zzId (Qeq_bool (zz_linform_r zz_pq_1 zz_as_1 zz_bs_1 3) zz_r_1) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_s_1 : zzId (Qeq_bool (zz_linform_s zz_as_1 zz_bs_1) zz_s_1) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_sym_1 : zzId (zz_lqeqb zz_as_1 zz_bs_1) true.
Proof. vm_compute. reflexivity. Qed.

(* ---- n=2：m=6·Pq 度 6·对照认证域系数表（极点序） ---- *)
Definition zz_pq_2 : list Q := [(-8952320#1)%Q; (0#1)%Q; (-110080#1)%Q; (0#1)%Q; (-995#1)%Q; (0#1)%Q; (-5#1)%Q].
Definition zz_as_2 : list Q := [(37324672#1)%Q; (-112234880#1)%Q; (256441600#1)%Q; (-431872000#1)%Q; (506880000#1)%Q; (-371200000#1)%Q; (128000000#1)%Q].
Definition zz_bs_2 : list Q := [(37324672#1)%Q; (-112234880#1)%Q; (256441600#1)%Q; (-431872000#1)%Q; (506880000#1)%Q; (-371200000#1)%Q; (128000000#1)%Q].
Definition zz_r_2 : Q := (-3078046528#105)%Q.
Definition zz_s_2 : Q := (9331168#1)%Q.

Lemma zz_bite_r_2 : zzId (Qeq_bool (zz_linform_r zz_pq_2 zz_as_2 zz_bs_2 6) zz_r_2) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_s_2 : zzId (Qeq_bool (zz_linform_s zz_as_2 zz_bs_2) zz_s_2) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_sym_2 : zzId (zz_lqeqb zz_as_2 zz_bs_2) true.
Proof. vm_compute. reflexivity. Qed.

(* ---- n=3：m=9·Pq 度 10·对照认证域系数表（极点序） ---- *)
Definition zz_pq_3 : list Q := [(161509153280#1)%Q; (0#1)%Q; (2145267200#1)%Q; (0#1)%Q; (24281600#1)%Q; (0#1)%Q; (220325#1)%Q; (0#1)%Q; (1430#1)%Q; (0#1)%Q; (5#1)%Q].
Definition zz_as_3 : list Q := [(-668063626240#1)%Q; (2039143325440#1)%Q; (-5189581721600#1)%Q; (10894872064000#1)%Q; (-18563676160000#1)%Q; (25054976000000#1)%Q; (-25802752000000#1)%Q; (19066880000000#1)%Q; (-9011200000000#1)%Q; (2048000000000#1)%Q].
Definition zz_bs_3 : list Q := [(-668063626240#1)%Q; (2039143325440#1)%Q; (-5189581721600#1)%Q; (10894872064000#1)%Q; (-18563676160000#1)%Q; (25054976000000#1)%Q; (-25802752000000#1)%Q; (19066880000000#1)%Q; (-9011200000000#1)%Q; (2048000000000#1)%Q].
Definition zz_r_3 : Q := (51944898563072#99)%Q.
Definition zz_s_3 : Q := (-167015906560#1)%Q.

Lemma zz_bite_r_3 : zzId (Qeq_bool (zz_linform_r zz_pq_3 zz_as_3 zz_bs_3 9) zz_r_3) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_s_3 : zzId (Qeq_bool (zz_linform_s zz_as_3 zz_bs_3) zz_s_3) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_sym_3 : zzId (zz_lqeqb zz_as_3 zz_bs_3) true.
Proof. vm_compute. reflexivity. Qed.

(* ---- n=4：m=12·Pq 度 14·对照认证域系数表（极点序） ---- *)
Definition zz_pq_4 : list Q := [(-3073295150141440#1)%Q; (0#1)%Q; (-42264953507840#1)%Q; (0#1)%Q; (-521977057280#1)%Q; (0#1)%Q; (-5639065600#1)%Q; (0#1)%Q; (-51262355#1)%Q; (0#1)%Q; (-368415#1)%Q; (0#1)%Q; (-1865#1)%Q; (0#1)%Q; (-5#1)%Q].
Definition zz_as_4 : list Q := [(12662481897547776#1)%Q; (-38940292322140160#1)%Q; (104528956649062400#1)%Q; (-243622731534336000#1)%Q; (489366644121600000#1)%Q; (-838753347174400000#1)%Q; (1210109689856000000#1)%Q; (-1442497495040000000#1)%Q; (1383769702400000000#1)%Q; (-1027244032000000000#1)%Q; (554106880000000000#1)%Q; (-193331200000000000#1)%Q; (32768000000000000#1)%Q].
Definition zz_bs_4 : list Q := [(12662481897547776#1)%Q; (-38940292322140160#1)%Q; (104528956649062400#1)%Q; (-243622731534336000#1)%Q; (489366644121600000#1)%Q; (-838753347174400000#1)%Q; (1210109689856000000#1)%Q; (-1442497495040000000#1)%Q; (1383769702400000000#1)%Q; (-1027244032000000000#1)%Q; (554106880000000000#1)%Q; (-193331200000000000#1)%Q; (32768000000000000#1)%Q].
Definition zz_r_4 : Q := (-5817877665436663808#585)%Q.
Definition zz_s_4 : Q := (3165620474386944#1)%Q.

Lemma zz_bite_r_4 : zzId (Qeq_bool (zz_linform_r zz_pq_4 zz_as_4 zz_bs_4 12) zz_r_4) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_s_4 : zzId (Qeq_bool (zz_linform_s zz_as_4 zz_bs_4) zz_s_4) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_sym_4 : zzId (zz_lqeqb zz_as_4 zz_bs_4) true.
Proof. vm_compute. reflexivity. Qed.

(* ---- n=5：m=15·Pq 度 18·对照认证域系数表（极点序） ---- *)
Definition zz_pq_5 : list Q := [(60264683735690444800#1)%Q; (0#1)%Q; (845328662657433600#1)%Q; (0#1)%Q; (10936371771801600#1)%Q; (0#1)%Q; (128613035212800#1)%Q; (0#1)%Q; (1348503797760#1)%Q; (0#1)%Q; (12272023925#1)%Q; (0#1)%Q; (93187100#1)%Q; (0#1)%Q; (554350#1)%Q; (0#1)%Q; (2300#1)%Q; (0#1)%Q; (5#1)%Q].
Definition zz_as_5 : list Q := [(-247718478176291684352#1)%Q; (765223105352073543680#1)%Q; (-2120565145396589363200#1)%Q; (5255061654375251968000#1)%Q; (-11597549724026142720000#1)%Q; (22672726593686732800000#1)%Q; (-38998131777339392000000#1)%Q; (58510012516270080000000#1)%Q; (-75723941032755200000000#1)%Q; (83318293659648000000000#1)%Q; (-76434526699520000000000#1)%Q; (56899521740800000000000#1)%Q; (-33029619712000000000000#1)%Q; (14029946880000000000000#1)%Q; (-3879731200000000000000#1)%Q; (524288000000000000000#1)%Q].
Definition zz_bs_5 : list Q := [(-247718478176291684352#1)%Q; (765223105352073543680#1)%Q; (-2120565145396589363200#1)%Q; (5255061654375251968000#1)%Q; (-11597549724026142720000#1)%Q; (22672726593686732800000#1)%Q; (-38998131777339392000000#1)%Q; (58510012516270080000000#1)%Q; (-75723941032755200000000#1)%Q; (83318293659648000000000#1)%Q; (-76434526699520000000000#1)%Q; (56899521740800000000000#1)%Q; (-33029619712000000000000#1)%Q; (14029946880000000000000#1)%Q; (-3879731200000000000000#1)%Q; (524288000000000000000#1)%Q].
Definition zz_r_5 : Q := (134796340984657486420639744#692835)%Q.
Definition zz_s_5 : Q := (-61929619544072921088#1)%Q.

Lemma zz_bite_r_5 : zzId (Qeq_bool (zz_linform_r zz_pq_5 zz_as_5 zz_bs_5 15) zz_r_5) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_s_5 : zzId (Qeq_bool (zz_linform_s zz_as_5 zz_bs_5) zz_s_5) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_sym_5 : zzId (zz_lqeqb zz_as_5 zz_bs_5) true.
Proof. vm_compute. reflexivity. Qed.

(* ---- n=6：m=18·Pq 度 22·对照认证域系数表（极点序） ---- *)
Definition zz_pq_6 : list Q := [(-1204778072334947762831360#1)%Q; (0#1)%Q; (-17116373597102294958080#1)%Q; (0#1)%Q; (-227930146700302745600#1)%Q; (0#1)%Q; (-2818825347570073600#1)%Q; (0#1)%Q; (-32002775315906560#1)%Q; (0#1)%Q; (-328631485726720#1)%Q; (0#1)%Q; (-2992842784835#1)%Q; (0#1)%Q; (-23523503225#1)%Q; (0#1)%Q; (-153348350#1)%Q; (0#1)%Q; (-778130#1)%Q; (0#1)%Q; (-2735#1)%Q; (0#1)%Q; (-5#1)%Q].
Definition zz_as_6 : list Q := [(4944532049049334682288128#1)%Q; (-15319820233235323294515200#1)%Q; (43362177968215378935808000#1)%Q; (-111890732928001562378240000#1)%Q; (262519043714604618219520000#1)%Q; (-558206953899620512563200000#1)%Q; (1071419325708343705600000000#1)%Q; (-1847260878819347660800000000#1)%Q; (2843799579988066304000000000#1)%Q; (-3880307023083470848000000000#1)%Q; (4649863484701409280000000000#1)%Q; (-4837053378330624000000000000#1)%Q; (4303128404951040000000000000#1)%Q; (-3209326860697600000000000000#1)%Q; (1952261026611200000000000000#1)%Q; (-930497953792000000000000000#1)%Q; (325981306880000000000000000#1)%Q; (-74658611200000000000000000#1)%Q; (8388608000000000000000000#1)%Q].
Definition zz_bs_6 : list Q := [(4944532049049334682288128#1)%Q; (-15319820233235323294515200#1)%Q; (43362177968215378935808000#1)%Q; (-111890732928001562378240000#1)%Q; (262519043714604618219520000#1)%Q; (-558206953899620512563200000#1)%Q; (1071419325708343705600000000#1)%Q; (-1847260878819347660800000000#1)%Q; (2843799579988066304000000000#1)%Q; (-3880307023083470848000000000#1)%Q; (4649863484701409280000000000#1)%Q; (-4837053378330624000000000000#1)%Q; (4303128404951040000000000000#1)%Q; (-3209326860697600000000000000#1)%Q; (1952261026611200000000000000#1)%Q; (-930497953792000000000000000#1)%Q; (325981306880000000000000000#1)%Q; (-74658611200000000000000000#1)%Q; (8388608000000000000000000#1)%Q].
Definition zz_r_6 : Q := (-118140646202686780368786468896768#30421755)%Q.
Definition zz_s_6 : Q := (1236133012262333670572032#1)%Q.

Lemma zz_bite_r_6 : zzId (Qeq_bool (zz_linform_r zz_pq_6 zz_as_6 zz_bs_6 18) zz_r_6) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_s_6 : zzId (Qeq_bool (zz_linform_s zz_as_6 zz_bs_6) zz_s_6) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_bite_sym_6 : zzId (zz_lqeqb zz_as_6 zz_bs_6) true.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* §4 非零性核心 Z 证书（层 2④缺口机形替代的算术核）：                            *)
(*    N(−5) = 5·4000^{2n} = 5^{3n}·2^{7n−1}·10^{3n+1} ⟹ 末位 Laurent 系数       *)
(*    = 5^{3n}·2^{7n−1} ≠ 0（与 Laurent 装配的接续＝切片 2-3·本片铸算术核）。     *)
(* ============================================================ *)

Lemma zz_nz_core_1 : zzId (Z.eqb ((5 * 4000 ^ 2)%Z) (80000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_nz_core_2 : zzId (Z.eqb ((5 * 4000 ^ 4)%Z) (1280000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_nz_core_3 : zzId (Z.eqb ((5 * 4000 ^ 6)%Z) (20480000000000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_nz_core_4 : zzId (Z.eqb ((5 * 4000 ^ 8)%Z) (327680000000000000000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_nz_core_5 : zzId (Z.eqb ((5 * 4000 ^ 10)%Z) (5242880000000000000000000000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_nz_core_6 : zzId (Z.eqb ((5 * 4000 ^ 12)%Z) (83886080000000000000000000000000000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.

(* 末位 Laurent 系数封闭式字面锚（对照 1a·n=1..6 位）：5^{3n}·2^{7n−1} *)
Lemma zz_closed_1 : zzId (Z.eqb ((5 ^ 3 * 2 ^ 6)%Z) (8000)%Z) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz_closed_2 : zzId (Z.eqb ((5 ^ 6 * 2 ^ 13)%Z) (128000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_closed_3 : zzId (Z.eqb ((5 ^ 9 * 2 ^ 20)%Z) (2048000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_closed_4 : zzId (Z.eqb ((5 ^ 12 * 2 ^ 27)%Z) (32768000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_closed_5 : zzId (Z.eqb ((5 ^ 15 * 2 ^ 34)%Z) (524288000000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz_closed_6 : zzId (Z.eqb ((5 ^ 18 * 2 ^ 41)%Z) (8388608000000000000000000)%Z) true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §5 提取与审计（零全局假设复核·提取差分面）                                     *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction zz_linform_r zz_linform_s zz_linform_sig_inst zz_res_q gz_im_neg_frac.

Print Assumptions zz_linform_sig_inst.
Print Assumptions zz_linform_r.
Print Assumptions zz_linform_s.
Print Assumptions zz_tab_ep_m1.
Print Assumptions zz_tab_ep_if4.
Print Assumptions zz_tab_ep_if6.
Print Assumptions zz_bite_r_1.
Print Assumptions zz_bite_s_1.
Print Assumptions zz_bite_r_6.
Print Assumptions zz_bite_s_6.
Print Assumptions zz_bite_sym_6.
Print Assumptions zz_nz_core_6.
Print Assumptions zz_closed_6.

