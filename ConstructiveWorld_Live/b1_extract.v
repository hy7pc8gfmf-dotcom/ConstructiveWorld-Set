(* ============================================================
   Module: b1_extract
   Mission. Extraction driver for the b1 spine: the nine constants
     b1_ps, b1_pq, b1_seg_poly, b1_seg_signed, b1_seg_beta, b1_rho,
     b1_dfact_odd, b1_dfact_even, b1_odd_div_dfact are extracted by a
     single Separate Extraction command into [extract/] (this file
     states no theorems). Sample contract, recomputable from the
     definitions: b1_ps 1 2 (1/2) = 11/4; b1_pq 2 3 (1/2) = 11/2;
     b1_seg_poly 1 1 = [0;0;0;2;-2] (integral 1/10);
     b1_seg_signed 1 1 = [0;0;0;-2;2] (integral -1/10);
     b1_seg_beta 1 1 = 1/20; b1_rho 1 1 = 1/15; b1_dfact_odd 4 = 105;
     b1_dfact_even 4 = 384; b1_odd_div_dfact 3 3 = 15 with 15*7 = 105.
   Dependencies. b1_kernel_pointwise, b1_trunc_master, b1_carrier_beta,
     b1_denom_control (proved Set-carrier modules); Stdlib Extraction.
   References. ConstructiveWorld-Main, module b1_extract; the module
     name, require list, and extraction list are carried over verbatim.
   Constructivity. This file defines no statements; every extracted
     constant originates from a proved Set-carrier module, and the
     extraction products are required to hold Obj.magic = 0 on both
     faces.
   Build. coqc -native-compiler no -q -Q <world> "" -o b1_extract.vo
     b1_extract.v, where <world> carries the compiled dependency
     closure; the Separate Extraction command fires during that run.
   ============================================================ *)

Require Import b1_kernel_pointwise.
Require Import b1_trunc_master.
Require Import b1_carrier_beta.
Require Import b1_denom_control.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "extract".

Separate Extraction b1_ps b1_pq b1_seg_poly b1_seg_signed b1_seg_beta
  b1_rho b1_dfact_odd b1_dfact_even b1_odd_div_dfact.
