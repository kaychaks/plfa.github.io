---
src       : "src/plfa/part1/Negation.lagda.md"
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
prev      : /Connectives/
permalink : /Negation/
next      : /Quantifiers/
---

{% raw %}<pre class="Agda"><a id="180" class="Keyword">module</a> <a id="187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}" class="Module">plfa.part1.Negation</a> <a id="207" class="Keyword">where</a>
</pre>{% endraw %}
This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

{% raw %}<pre class="Agda"><a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="https://agda.github.io/agda-stdlib/v1.3/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="369" class="Keyword">using</a> <a id="375" class="Symbol">(</a><a id="376" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="379" class="Symbol">;</a> <a id="381" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="385" class="Symbol">)</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="https://agda.github.io/agda-stdlib/v1.3/Data.Nat.html" class="Module">Data.Nat</a> <a id="408" class="Keyword">using</a> <a id="414" class="Symbol">(</a><a id="415" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a><a id="416" class="Symbol">;</a> <a id="418" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a><a id="422" class="Symbol">;</a> <a id="424" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a><a id="427" class="Symbol">)</a>
<a id="429" class="Keyword">open</a> <a id="434" class="Keyword">import</a> <a id="441" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html" class="Module">Data.Empty</a> <a id="452" class="Keyword">using</a> <a id="458" class="Symbol">(</a><a id="459" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a><a id="460" class="Symbol">;</a> <a id="462" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#628" class="Function">⊥-elim</a><a id="468" class="Symbol">)</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.html" class="Module">Data.Sum</a> <a id="491" class="Keyword">using</a> <a id="497" class="Symbol">(</a><a id="498" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#728" class="Datatype Operator">_⊎_</a><a id="501" class="Symbol">;</a> <a id="503" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#778" class="InductiveConstructor">inj₁</a><a id="507" class="Symbol">;</a> <a id="509" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#803" class="InductiveConstructor">inj₂</a><a id="513" class="Symbol">)</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="https://agda.github.io/agda-stdlib/v1.3/Data.Product.html" class="Module">Data.Product</a> <a id="540" class="Keyword">using</a> <a id="546" class="Symbol">(</a><a id="547" href="https://agda.github.io/agda-stdlib/v1.3/Data.Product.html#1167" class="Function Operator">_×_</a><a id="550" class="Symbol">)</a>
<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}" class="Module">plfa.part1.Isomorphism</a> <a id="587" class="Keyword">using</a> <a id="593" class="Symbol">(</a><a id="594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#4365" class="Record Operator">_≃_</a><a id="597" class="Symbol">;</a> <a id="599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2684" class="Postulate">extensionality</a><a id="613" class="Symbol">)</a>
</pre>{% endraw %}

## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false:
{% raw %}<pre class="Agda"><a id="¬_"></a><a id="793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬_</a> <a id="796" class="Symbol">:</a> <a id="798" class="PrimitiveType">Set</a> <a id="802" class="Symbol">→</a> <a id="804" class="PrimitiveType">Set</a>
<a id="808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#810" class="Bound">A</a> <a id="812" class="Symbol">=</a> <a id="814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#810" class="Bound">A</a> <a id="816" class="Symbol">→</a> <a id="818" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a>
</pre>{% endraw %}This is a form of _reductio ad absurdum_: if assuming `A` leads
to the conclusion `⊥` (an absurdity), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction:
{% raw %}<pre class="Agda"><a id="¬-elim"></a><a id="1369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1369" class="Function">¬-elim</a> <a id="1376" class="Symbol">:</a> <a id="1378" class="Symbol">∀</a> <a id="1380" class="Symbol">{</a><a id="1381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1381" class="Bound">A</a> <a id="1383" class="Symbol">:</a> <a id="1385" class="PrimitiveType">Set</a><a id="1388" class="Symbol">}</a>
  <a id="1392" class="Symbol">→</a> <a id="1394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="1396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1381" class="Bound">A</a>
  <a id="1400" class="Symbol">→</a> <a id="1402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1381" class="Bound">A</a>
    <a id="1408" class="Comment">---</a>
  <a id="1414" class="Symbol">→</a> <a id="1416" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a>
<a id="1418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1369" class="Function">¬-elim</a> <a id="1425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1425" class="Bound">¬x</a> <a id="1428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1428" class="Bound">x</a> <a id="1430" class="Symbol">=</a> <a id="1432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1425" class="Bound">¬x</a> <a id="1435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#1428" class="Bound">x</a>
</pre>{% endraw %}Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else:
{% raw %}<pre class="Agda"><a id="1820" class="Keyword">infix</a> <a id="1826" class="Number">3</a> <a id="1828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬_</a>
</pre>{% endraw %}Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In _classical_ logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use _intuitionistic_ logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`:
{% raw %}<pre class="Agda"><a id="¬¬-intro"></a><a id="2117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2117" class="Function">¬¬-intro</a> <a id="2126" class="Symbol">:</a> <a id="2128" class="Symbol">∀</a> <a id="2130" class="Symbol">{</a><a id="2131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2131" class="Bound">A</a> <a id="2133" class="Symbol">:</a> <a id="2135" class="PrimitiveType">Set</a><a id="2138" class="Symbol">}</a>
  <a id="2142" class="Symbol">→</a> <a id="2144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2131" class="Bound">A</a>
    <a id="2150" class="Comment">-----</a>
  <a id="2158" class="Symbol">→</a> <a id="2160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2131" class="Bound">A</a>
<a id="2166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2117" class="Function">¬¬-intro</a> <a id="2175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2175" class="Bound">x</a>  <a id="2178" class="Symbol">=</a>  <a id="2181" class="Symbol">λ{</a><a id="2183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2183" class="Bound">¬x</a> <a id="2186" class="Symbol">→</a> <a id="2188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2183" class="Bound">¬x</a> <a id="2191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2175" class="Bound">x</a><a id="2192" class="Symbol">}</a>
</pre>{% endraw %}Let `x` be evidence of `A`. We show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

An equivalent way to write the above is as follows:
{% raw %}<pre class="Agda"><a id="¬¬-intro′"></a><a id="2499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2499" class="Function">¬¬-intro′</a> <a id="2509" class="Symbol">:</a> <a id="2511" class="Symbol">∀</a> <a id="2513" class="Symbol">{</a><a id="2514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2514" class="Bound">A</a> <a id="2516" class="Symbol">:</a> <a id="2518" class="PrimitiveType">Set</a><a id="2521" class="Symbol">}</a>
  <a id="2525" class="Symbol">→</a> <a id="2527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2514" class="Bound">A</a>
    <a id="2533" class="Comment">-----</a>
  <a id="2541" class="Symbol">→</a> <a id="2543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2514" class="Bound">A</a>
<a id="2549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2499" class="Function">¬¬-intro′</a> <a id="2559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2559" class="Bound">x</a> <a id="2561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2561" class="Bound">¬x</a> <a id="2564" class="Symbol">=</a> <a id="2566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2561" class="Bound">¬x</a> <a id="2569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2559" class="Bound">x</a>
</pre>{% endraw %}Here we have simply converted the argument of the lambda term
to an additional argument of the function.  We will usually
use this latter style, as it is more compact.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`:
{% raw %}<pre class="Agda"><a id="¬¬¬-elim"></a><a id="2835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2835" class="Function">¬¬¬-elim</a> <a id="2844" class="Symbol">:</a> <a id="2846" class="Symbol">∀</a> <a id="2848" class="Symbol">{</a><a id="2849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2849" class="Bound">A</a> <a id="2851" class="Symbol">:</a> <a id="2853" class="PrimitiveType">Set</a><a id="2856" class="Symbol">}</a>
  <a id="2860" class="Symbol">→</a> <a id="2862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2864" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2849" class="Bound">A</a>
    <a id="2874" class="Comment">-------</a>
  <a id="2884" class="Symbol">→</a> <a id="2886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="2888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2849" class="Bound">A</a>
<a id="2890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2835" class="Function">¬¬¬-elim</a> <a id="2899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2899" class="Bound">¬¬¬x</a>  <a id="2905" class="Symbol">=</a>  <a id="2908" class="Symbol">λ</a> <a id="2910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2910" class="Bound">x</a> <a id="2912" class="Symbol">→</a> <a id="2914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2899" class="Bound">¬¬¬x</a> <a id="2919" class="Symbol">(</a><a id="2920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2117" class="Function">¬¬-intro</a> <a id="2929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#2910" class="Bound">x</a><a id="2930" class="Symbol">)</a>
</pre>{% endraw %}Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is _contraposition_,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`:
{% raw %}<pre class="Agda"><a id="contraposition"></a><a id="3392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3392" class="Function">contraposition</a> <a id="3407" class="Symbol">:</a> <a id="3409" class="Symbol">∀</a> <a id="3411" class="Symbol">{</a><a id="3412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3412" class="Bound">A</a> <a id="3414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3414" class="Bound">B</a> <a id="3416" class="Symbol">:</a> <a id="3418" class="PrimitiveType">Set</a><a id="3421" class="Symbol">}</a>
  <a id="3425" class="Symbol">→</a> <a id="3427" class="Symbol">(</a><a id="3428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3412" class="Bound">A</a> <a id="3430" class="Symbol">→</a> <a id="3432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3414" class="Bound">B</a><a id="3433" class="Symbol">)</a>
    <a id="3439" class="Comment">-----------</a>
  <a id="3453" class="Symbol">→</a> <a id="3455" class="Symbol">(</a><a id="3456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="3458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3414" class="Bound">B</a> <a id="3460" class="Symbol">→</a> <a id="3462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="3464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3412" class="Bound">A</a><a id="3465" class="Symbol">)</a>
<a id="3467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3392" class="Function">contraposition</a> <a id="3482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3482" class="Bound">f</a> <a id="3484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3484" class="Bound">¬y</a> <a id="3487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3487" class="Bound">x</a> <a id="3489" class="Symbol">=</a> <a id="3491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3484" class="Bound">¬y</a> <a id="3494" class="Symbol">(</a><a id="3495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3482" class="Bound">f</a> <a id="3497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3487" class="Bound">x</a><a id="3498" class="Symbol">)</a>
</pre>{% endraw %}Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence `¬ A`
must hold. Let `x` be evidence of `A`.  Then from `A → B` and `A` we
may conclude `B`, evidenced by `f x`, and from `B` and `¬ B` we may
conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown `¬ A`.

Using negation, it is straightforward to define inequality:
{% raw %}<pre class="Agda"><a id="_≢_"></a><a id="3914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3914" class="Function Operator">_≢_</a> <a id="3918" class="Symbol">:</a> <a id="3920" class="Symbol">∀</a> <a id="3922" class="Symbol">{</a><a id="3923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3923" class="Bound">A</a> <a id="3925" class="Symbol">:</a> <a id="3927" class="PrimitiveType">Set</a><a id="3930" class="Symbol">}</a> <a id="3932" class="Symbol">→</a> <a id="3934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3923" class="Bound">A</a> <a id="3936" class="Symbol">→</a> <a id="3938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3923" class="Bound">A</a> <a id="3940" class="Symbol">→</a> <a id="3942" class="PrimitiveType">Set</a>
<a id="3946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3946" class="Bound">x</a> <a id="3948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3914" class="Function Operator">≢</a> <a id="3950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3950" class="Bound">y</a>  <a id="3953" class="Symbol">=</a>  <a id="3956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="3958" class="Symbol">(</a><a id="3959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3946" class="Bound">x</a> <a id="3961" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="3963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3950" class="Bound">y</a><a id="3964" class="Symbol">)</a>
</pre>{% endraw %}It is trivial to show distinct numbers are not equal:
{% raw %}<pre class="Agda"><a id="4028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4028" class="Function">_</a> <a id="4030" class="Symbol">:</a> <a id="4032" class="Number">1</a> <a id="4034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3914" class="Function Operator">≢</a> <a id="4036" class="Number">2</a>
<a id="4038" class="Symbol">_</a> <a id="4040" class="Symbol">=</a> <a id="4042" class="Symbol">λ()</a>
</pre>{% endraw %}This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number:
{% raw %}<pre class="Agda"><a id="peano"></a><a id="4435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4435" class="Function">peano</a> <a id="4441" class="Symbol">:</a> <a id="4443" class="Symbol">∀</a> <a id="4445" class="Symbol">{</a><a id="4446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4446" class="Bound">m</a> <a id="4448" class="Symbol">:</a> <a id="4450" href="Agda.Builtin.Nat.html#192" class="Datatype">ℕ</a><a id="4451" class="Symbol">}</a> <a id="4453" class="Symbol">→</a> <a id="4455" href="Agda.Builtin.Nat.html#210" class="InductiveConstructor">zero</a> <a id="4460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#3914" class="Function Operator">≢</a> <a id="4462" href="Agda.Builtin.Nat.html#223" class="InductiveConstructor">suc</a> <a id="4466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4446" class="Bound">m</a>
<a id="4468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4435" class="Function">peano</a> <a id="4474" class="Symbol">=</a> <a id="4476" class="Symbol">λ()</a>
</pre>{% endraw %}The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.  We can write
this proof two different ways:
{% raw %}<pre class="Agda"><a id="id"></a><a id="4962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4962" class="Function">id</a> <a id="4965" class="Symbol">:</a> <a id="4967" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a> <a id="4969" class="Symbol">→</a> <a id="4971" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a>
<a id="4973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4962" class="Function">id</a> <a id="4976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4976" class="Bound">x</a> <a id="4978" class="Symbol">=</a> <a id="4980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4976" class="Bound">x</a>

<a id="id′"></a><a id="4983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4983" class="Function">id′</a> <a id="4987" class="Symbol">:</a> <a id="4989" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a> <a id="4991" class="Symbol">→</a> <a id="4993" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#526" class="Datatype">⊥</a>
<a id="4995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4983" class="Function">id′</a> <a id="4999" class="Symbol">()</a>
</pre>{% endraw %}But, using extensionality, we can prove these equal:
{% raw %}<pre class="Agda"><a id="id≡id′"></a><a id="5063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5063" class="Function">id≡id′</a> <a id="5070" class="Symbol">:</a> <a id="5072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4962" class="Function">id</a> <a id="5075" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#4983" class="Function">id′</a>
<a id="5081" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5063" class="Function">id≡id′</a> <a id="5088" class="Symbol">=</a> <a id="5090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2684" class="Postulate">extensionality</a> <a id="5105" class="Symbol">(λ())</a>
</pre>{% endraw %}By extensionality, `id ≡ id′` holds if for every
`x` in their domain we have `id x ≡ id′ x`. But there
is no `x` in their domain, so the equality holds trivially.

Indeed, we can show any two proofs of a negation are equal:
{% raw %}<pre class="Agda"><a id="assimilation"></a><a id="5343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5343" class="Function">assimilation</a> <a id="5356" class="Symbol">:</a> <a id="5358" class="Symbol">∀</a> <a id="5360" class="Symbol">{</a><a id="5361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5361" class="Bound">A</a> <a id="5363" class="Symbol">:</a> <a id="5365" class="PrimitiveType">Set</a><a id="5368" class="Symbol">}</a> <a id="5370" class="Symbol">(</a><a id="5371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5371" class="Bound">¬x</a> <a id="5374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5374" class="Bound">¬x′</a> <a id="5378" class="Symbol">:</a> <a id="5380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="5382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5361" class="Bound">A</a><a id="5383" class="Symbol">)</a> <a id="5385" class="Symbol">→</a> <a id="5387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5371" class="Bound">¬x</a> <a id="5390" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5374" class="Bound">¬x′</a>
<a id="5396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5343" class="Function">assimilation</a> <a id="5409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5409" class="Bound">¬x</a> <a id="5412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5412" class="Bound">¬x′</a> <a id="5416" class="Symbol">=</a> <a id="5418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Isomorphism.md %}{% raw %}#2684" class="Postulate">extensionality</a> <a id="5433" class="Symbol">(λ</a> <a id="5436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5436" class="Bound">x</a> <a id="5438" class="Symbol">→</a> <a id="5440" href="https://agda.github.io/agda-stdlib/v1.3/Data.Empty.html#628" class="Function">⊥-elim</a> <a id="5447" class="Symbol">(</a><a id="5448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5409" class="Bound">¬x</a> <a id="5451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#5436" class="Bound">x</a><a id="5452" class="Symbol">))</a>
</pre>{% endraw %}Evidence for `¬ A` implies that any evidence of `A`
immediately leads to a contradiction.  But extensionality
quantifies over all `x` such that `A` holds, hence any
such `x` immediately leads to a contradiction,
again causing the equality to hold trivially.


#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

{% raw %}<pre class="Agda"><a id="5915" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

{% raw %}<pre class="Agda"><a id="6325" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

{% raw %}<pre class="Agda"><a id="6597" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?


## Intuitive and Classical logic

In Gilbert and Sullivan's _The Gondoliers_, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
_classical_ and _intuitionistic_. Intuitionists, concerned
by assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
_which_ of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded middle, which
asserts `A ⊎ ¬ A` for every `A`, since the law gives no clue as to
_which_ of `A` or `¬ A` holds. Heyting formalised a variant of
Hilbert's classical logic that captures the intuitionistic notion of
provability. In particular, the law of the excluded middle is provable
in Hilbert's logic, but not in Heyting's.  Further, if the law of the
excluded middle is added as an axiom to Heyting's logic, then it
becomes equivalent to Hilbert's.  Kolmogorov showed the two logics
were closely related: he gave a double-negation translation, such that
a formula is provable in classical logic if and only if its
translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
_Communications of the ACM_, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows:
{% raw %}<pre class="Agda"><a id="9133" class="Keyword">postulate</a>
  <a id="em"></a><a id="9145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9145" class="Postulate">em</a> <a id="9148" class="Symbol">:</a> <a id="9150" class="Symbol">∀</a> <a id="9152" class="Symbol">{</a><a id="9153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9153" class="Bound">A</a> <a id="9155" class="Symbol">:</a> <a id="9157" class="PrimitiveType">Set</a><a id="9160" class="Symbol">}</a> <a id="9162" class="Symbol">→</a> <a id="9164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9153" class="Bound">A</a> <a id="9166" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#728" class="Datatype Operator">⊎</a> <a id="9168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9153" class="Bound">A</a>
</pre>{% endraw %}As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is _irrefutable_,
meaning that the negation of its negation is provable (and hence that
its negation is never provable):
{% raw %}<pre class="Agda"><a id="em-irrefutable"></a><a id="9414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9414" class="Function">em-irrefutable</a> <a id="9429" class="Symbol">:</a> <a id="9431" class="Symbol">∀</a> <a id="9433" class="Symbol">{</a><a id="9434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9434" class="Bound">A</a> <a id="9436" class="Symbol">:</a> <a id="9438" class="PrimitiveType">Set</a><a id="9441" class="Symbol">}</a> <a id="9443" class="Symbol">→</a> <a id="9445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9449" class="Symbol">(</a><a id="9450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9434" class="Bound">A</a> <a id="9452" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#728" class="Datatype Operator">⊎</a> <a id="9454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="9456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9434" class="Bound">A</a><a id="9457" class="Symbol">)</a>
<a id="9459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9414" class="Function">em-irrefutable</a> <a id="9474" class="Symbol">=</a> <a id="9476" class="Symbol">λ</a> <a id="9478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9478" class="Bound">k</a> <a id="9480" class="Symbol">→</a> <a id="9482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9478" class="Bound">k</a> <a id="9484" class="Symbol">(</a><a id="9485" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#803" class="InductiveConstructor">inj₂</a> <a id="9490" class="Symbol">(λ</a> <a id="9493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9493" class="Bound">x</a> <a id="9495" class="Symbol">→</a> <a id="9497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9478" class="Bound">k</a> <a id="9499" class="Symbol">(</a><a id="9500" href="https://agda.github.io/agda-stdlib/v1.3/Data.Sum.Base.html#778" class="InductiveConstructor">inj₁</a> <a id="9505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#9493" class="Bound">x</a><a id="9506" class="Symbol">)))</a>
</pre>{% endraw %}The best way to explain this code is to develop it interactively:

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that given a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly:

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct:

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, the only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly:

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct:

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, _International Conference on Functional Programming_, 2003.)


#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

{% raw %}<pre class="Agda"><a id="12895" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
{% raw %}<pre class="Agda"><a id="Stable"></a><a id="13038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13038" class="Function">Stable</a> <a id="13045" class="Symbol">:</a> <a id="13047" class="PrimitiveType">Set</a> <a id="13051" class="Symbol">→</a> <a id="13053" class="PrimitiveType">Set</a>
<a id="13057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13038" class="Function">Stable</a> <a id="13064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13064" class="Bound">A</a> <a id="13066" class="Symbol">=</a> <a id="13068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="13070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#793" class="Function Operator">¬</a> <a id="13072" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13064" class="Bound">A</a> <a id="13074" class="Symbol">→</a> <a id="13076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/part1/Negation.md %}{% raw %}#13064" class="Bound">A</a>
</pre>{% endraw %}Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

{% raw %}<pre class="Agda"><a id="13187" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library:
{% raw %}<pre class="Agda"><a id="13323" class="Keyword">import</a> <a id="13330" href="https://agda.github.io/agda-stdlib/v1.3/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="13347" class="Keyword">using</a> <a id="13353" class="Symbol">(</a><a id="13354" href="https://agda.github.io/agda-stdlib/v1.3/Relation.Nullary.html#653" class="Function Operator">¬_</a><a id="13356" class="Symbol">)</a>
<a id="13358" class="Keyword">import</a> <a id="13365" href="https://agda.github.io/agda-stdlib/v1.3/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="13391" class="Keyword">using</a> <a id="13397" class="Symbol">(</a><a id="13398" href="https://agda.github.io/agda-stdlib/v1.3/Relation.Nullary.Negation.html#929" class="Function">contraposition</a><a id="13412" class="Symbol">)</a>
</pre>{% endraw %}
## Unicode

This chapter uses the following unicode:

    ¬  U+00AC  NOT SIGN (\neg)
    ≢  U+2262  NOT IDENTICAL TO (\==n)
