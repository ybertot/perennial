From Perennial.Helpers Require Import List.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From iris_string_ident Require Import ltac2_string_ident.

Inductive encodable :=
| EncUInt64 (x:u64)
| EncUInt32 (x:u32)
| EncBytes (bs:list u8)
.

Local Definition Rec := list encodable.

Local Definition encode1 (e:encodable) : list u8 :=
  match e with
  | EncUInt64 x => u64_le x
  | EncUInt32 x => u32_le x
  | EncBytes bs => bs
  end.

Local Definition encode (es:Rec): list u8 := concat (encode1 <$> es).

Local Definition encoded_length (r:Rec): nat := length $ encode r.

Theorem encode_app es1 es2 :
  encode (es1 ++ es2) = encode es1 ++ encode es2.
Proof.
  rewrite /encode.
  rewrite fmap_app.
  rewrite concat_app //.
Qed.

Theorem encode_singleton x :
  encode [x] = encode1 x.
Proof.
  rewrite /encode /=.
  rewrite app_nil_r //.
Qed.

Theorem encoded_length_app (r1 r2:Rec) :
  encoded_length (r1 ++ r2) = (encoded_length r1 + encoded_length r2)%nat.
Proof.
  rewrite /encoded_length.
  rewrite encode_app /=.
  len.
Qed.

Theorem encoded_length_app1 (r:Rec) (x:encodable) :
  encoded_length (r ++ [x]) = (encoded_length r + length (encode1 x))%nat.
Proof.
  rewrite encoded_length_app.
  f_equal.
  rewrite /encoded_length encode_singleton //.
Qed.

Section goose_lang.
Context `{!heapG Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types (v:val).

Definition has_encoding (data: list u8) (r:Rec) :=
  take (encoded_length r) data = encode r.

Definition is_enc (enc_v:val) (sz:Z) (r: Rec) (remaining: Z) : iProp Σ :=
  ∃ (s: Slice.t) (off_l: loc) (data: list u8),
    let off := encoded_length r in
    "->" ∷ ⌜enc_v = (slice_val s, (#off_l, #()))%V⌝ ∗
    "Hs" ∷ is_slice_small s byteT 1 data ∗
    "Hs_cap" ∷ is_slice_cap s byteT ∗
    "%Hsz" ∷ ⌜length data = Z.to_nat sz⌝ ∗
    "%Hremaining" ∷ ⌜(off + remaining)%Z = sz⌝ ∗
    "Hoff" ∷ off_l ↦[uint64T] #off ∗
    "%Hoff" ∷ ⌜0 ≤ off ≤ length data⌝ ∗
    "%Hencoded" ∷ ⌜has_encoding data r⌝
.

Theorem wp_new_enc stk E (sz: u64) :
  {{{ True }}}
    NewEnc #sz @ stk; E
  {{{ (enc_v:val), RET enc_v; is_enc enc_v (int.val sz) [] (int.val sz) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_NewSlice (V:=u8)).
  iIntros (s) "Hs".
  iDestruct (is_slice_split with "Hs") as "[Hs Hcap]".
  wp_apply (typed_mem.wp_AllocAt uint64T); eauto.
  iIntros (off_l) "Hoff".
  wp_pures.
  iApply "HΦ".
  iExists _, _, _; iFrame.
  iPureIntro.
  split_and!; auto; len.
  - rewrite /encoded_length /=; lia.
  - rewrite /encoded_length //=.
Qed.

Hint Unfold encoded_length : word.

Lemma has_encoding_app data r data' r' :
  has_encoding data r →
  has_encoding data' r' →
  has_encoding (take (encoded_length r) data ++ data')
                (r ++ r').
Proof.
  rewrite /has_encoding; intros.
  rewrite encoded_length_app.
  rewrite encode_app.
  rewrite H.
  rewrite -> take_app_ge by word.
  f_equal.
  replace (encoded_length r + encoded_length r' - length (encode r))%nat
    with (encoded_length r') by word.
  auto.
Qed.

Lemma has_encoding_app_prefix data1 data2 r :
  has_encoding data1 r →
  has_encoding (data1 ++ data2) r.
Proof.
  rewrite /has_encoding; intros.
  rewrite take_app_le //.
  apply (f_equal length) in H.
  move: H; len.
Qed.

Lemma has_encoding_exact data r :
  encode r = data →
  has_encoding data r.
Proof.
  intros <-.
  rewrite /has_encoding.
  rewrite take_ge //.
Qed.

Theorem wp_Enc__PutInt stk E enc_v sz r (x:u64) remaining :
  8 ≤ remaining →
  {{{ is_enc enc_v sz r remaining }}}
    Enc__PutInt enc_v #x @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ [EncUInt64 x]) (remaining - 8) }}}.
Proof.
  iIntros (Hspace Φ) "Hpre HΦ"; iNamed "Hpre".
  set (off:=encoded_length r) in *.
  wp_call.
  wp_load.
  wp_pures.
  iDestruct (is_slice_small_sz with "Hs") as %Hslice_len.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    word. }
  iDestruct (is_slice_small_take_drop _ _ _ (U64 off) with "Hs") as "[Hs2 Hs1]".
  { word. }
  replace (int.nat (U64 off)) with off by word.
  wp_apply (wp_UInt64Put with "[$Hs2]").
  { iPureIntro.
    len. }
  iIntros "Hs2".
  iDestruct (is_slice_combine with "Hs1 Hs2") as "Hs"; first len.
  wp_pures.
  wp_load; wp_store.
  rewrite drop_drop.
  iApply "HΦ".
  iExists _, _, _; iFrame.
  rewrite -fmap_take -fmap_drop.
  change (u64_le_bytes x) with (into_val.to_val (V:=u8) <$> u64_le x).
  rewrite -!fmap_app.
  iSplitR; first eauto.
  iFrame "Hs".
  rewrite encoded_length_app1.
  change (length (encode1 (EncUInt64 x))) with 8%nat.
  iSplitR; first by iPureIntro; len.
  iSplitR; first by iPureIntro; len.
  iSplitL "Hoff".
  { iExactEq "Hoff".
    rewrite /named.
    repeat (f_equal; try word). }
  iPureIntro; split.
  - len.
  - subst off.
    apply has_encoding_app; auto.
    apply has_encoding_app_prefix.
    apply has_encoding_exact.
    reflexivity.
Qed.

Theorem wp_Enc__PutInts stk E enc_v sz r (x_s: Slice.t) q (xs:list u64) remaining :
  8*(Z.of_nat $ length xs) ≤ remaining →
  {{{ is_enc enc_v sz r remaining ∗ is_slice_small x_s uint64T q xs }}}
    Enc__PutInts enc_v (slice_val x_s) @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ (EncUInt64 <$> xs)) (remaining - 8*(Z.of_nat $ length xs)) ∗
               is_slice_small x_s uint64T q xs }}}.
Proof.
  iIntros (Hbound Φ) "[Henc Hxs] HΦ".
  wp_rec; wp_pures.
  wp_apply (wp_forSlicePrefix
              (λ done todo,
                "%Hlen" ∷ ⌜length done + length todo ≤ length xs⌝ ∗
                "Henc" ∷ is_enc enc_v sz
                        (r ++ (EncUInt64 <$> done))
                        (remaining - 8*(Z.of_nat $ length done)))%I
           with "[] [$Hxs Henc]").
  - clear Φ.
    iIntros (????) "!>".
    iIntros (Φ) "HI HΦ"; iNamed "HI".
    wp_pures.
    wp_apply (wp_Enc__PutInt with "Henc").
    { move: Hlen; rewrite /=; len. }
    iIntros "Henc".
    iApply "HΦ".
    iSplit.
    { iPureIntro.
      move: Hlen; len. }
    iExactEq "Henc".
    rewrite /named; f_equal; len.
    rewrite fmap_app.
    rewrite -!app_assoc.
    reflexivity.
  - iSplit; first by len.
    iExactEq "Henc".
    rewrite /named; f_equal; len.
    rewrite app_nil_r //.
  - iIntros "(Hs&HI)"; iNamed "HI".
    iApply "HΦ"; iFrame.
Qed.

Theorem wp_enc_finish stk E enc_v r sz remaining :
  {{{ is_enc enc_v sz r remaining }}}
    Enc__Finish enc_v @ stk; E
  {{{ s data, RET slice_val s; is_slice s byteT 1 data ∗ ⌜has_encoding data r⌝ }}}.
Proof.
  iIntros (Φ) "Henc HΦ"; iNamed "Henc"; subst.
  wp_call.
  iApply "HΦ"; iFrame "∗ %".
Qed.

Definition is_dec (dec_v:val) (r:Rec) (data:list u8) : iProp Σ.
Admitted.

End goose_lang.
