---
src       : src/plfa/Induction.lagda
title     : "Induction: Proof by Induction"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
---

<pre class="Agda">{% raw %}<a id="155" class="Keyword">module</a> <a id="162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}" class="Module">plfa.Induction</a> <a id="177" class="Keyword">where</a>{% endraw %}</pre>

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.


## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
<pre class="Agda">{% raw %}<a id="788" class="Keyword">import</a> <a id="795" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="833" class="Symbol">as</a> <a id="836" class="Module">Eq</a>
<a id="839" class="Keyword">open</a> <a id="844" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="847" class="Keyword">using</a> <a id="853" class="Symbol">(</a><a id="854" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="857" class="Symbol">;</a> <a id="859" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="863" class="Symbol">;</a> <a id="865" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="869" class="Symbol">;</a> <a id="871" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="874" class="Symbol">)</a>
<a id="876" class="Keyword">open</a> <a id="881" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#3975" class="Module">Eq.≡-Reasoning</a> <a id="896" class="Keyword">using</a> <a id="902" class="Symbol">(</a><a id="903" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin_</a><a id="909" class="Symbol">;</a> <a id="911" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">_≡⟨⟩_</a><a id="916" class="Symbol">;</a> <a id="918" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">_≡⟨_⟩_</a><a id="924" class="Symbol">;</a> <a id="926" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">_∎</a><a id="928" class="Symbol">)</a>
<a id="930" class="Keyword">open</a> <a id="935" class="Keyword">import</a> <a id="942" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="951" class="Keyword">using</a> <a id="957" class="Symbol">(</a><a id="958" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="959" class="Symbol">;</a> <a id="961" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="965" class="Symbol">;</a> <a id="967" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="970" class="Symbol">;</a> <a id="972" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="975" class="Symbol">;</a> <a id="977" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="980" class="Symbol">;</a> <a id="982" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="985" class="Symbol">)</a>{% endraw %}</pre>


## Properties of operators

Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutativity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.

Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.

<pre class="Agda">{% raw %}<a id="3016" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables:
<pre class="Agda">{% raw %}<a id="3389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#3389" class="Function">_</a> <a id="3391" class="Symbol">:</a> <a id="3393" class="Symbol">(</a><a id="3394" class="Number">3</a> <a id="3396" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3398" class="Number">4</a><a id="3399" class="Symbol">)</a> <a id="3401" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3403" class="Number">5</a> <a id="3405" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3407" class="Number">3</a> <a id="3409" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3411" class="Symbol">(</a><a id="3412" class="Number">4</a> <a id="3414" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3416" class="Number">5</a><a id="3417" class="Symbol">)</a>
<a id="3419" class="Symbol">_</a> <a id="3421" class="Symbol">=</a>
  <a id="3425" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="3435" class="Symbol">(</a><a id="3436" class="Number">3</a> <a id="3438" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3440" class="Number">4</a><a id="3441" class="Symbol">)</a> <a id="3443" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3445" class="Number">5</a>
  <a id="3449" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="3457" class="Number">7</a> <a id="3459" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3461" class="Number">5</a>
  <a id="3465" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="3473" class="Number">12</a>
  <a id="3478" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="3486" class="Number">3</a> <a id="3488" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3490" class="Number">9</a>
  <a id="3494" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="3502" class="Number">3</a> <a id="3504" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3506" class="Symbol">(</a><a id="3507" class="Number">4</a> <a id="3509" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3511" class="Number">5</a><a id="3512" class="Symbol">)</a>
  <a id="3516" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.


## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need to prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties:

    -- In the beginning, no properties are known.

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply:

    -- On the first day, one property is known.
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today:

    -- On the second day, two properties are known.
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new:

    -- On the third day, three properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now:

    -- On the fourth day, four properties are known.
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property:

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof:
<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="7760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="7768" class="Symbol">:</a> <a id="7770" class="Symbol">∀</a> <a id="7772" class="Symbol">(</a><a id="7773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7773" class="Bound">m</a> <a id="7775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7775" class="Bound">n</a> <a id="7777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7777" class="Bound">p</a> <a id="7779" class="Symbol">:</a> <a id="7781" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7782" class="Symbol">)</a> <a id="7784" class="Symbol">→</a> <a id="7786" class="Symbol">(</a><a id="7787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7773" class="Bound">m</a> <a id="7789" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7775" class="Bound">n</a><a id="7792" class="Symbol">)</a> <a id="7794" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7777" class="Bound">p</a> <a id="7798" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7773" class="Bound">m</a> <a id="7802" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7804" class="Symbol">(</a><a id="7805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7775" class="Bound">n</a> <a id="7807" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7777" class="Bound">p</a><a id="7810" class="Symbol">)</a>
<a id="7812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="7820" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7825" class="Bound">n</a> <a id="7827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7827" class="Bound">p</a> <a id="7829" class="Symbol">=</a>
  <a id="7833" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="7843" class="Symbol">(</a><a id="7844" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7849" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7825" class="Bound">n</a><a id="7852" class="Symbol">)</a> <a id="7854" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7827" class="Bound">p</a>
  <a id="7860" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="7868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7825" class="Bound">n</a> <a id="7870" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7827" class="Bound">p</a>
  <a id="7876" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
   <a id="7883" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7888" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7890" class="Symbol">(</a><a id="7891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7825" class="Bound">n</a> <a id="7893" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7827" class="Bound">p</a><a id="7896" class="Symbol">)</a>
  <a id="7900" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="7902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="7910" class="Symbol">(</a><a id="7911" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a><a id="7916" class="Symbol">)</a> <a id="7918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a> <a id="7920" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a> <a id="7922" class="Symbol">=</a>
  <a id="7926" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="7936" class="Symbol">(</a><a id="7937" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a> <a id="7943" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a><a id="7946" class="Symbol">)</a> <a id="7948" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a>
  <a id="7954" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="7962" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7966" class="Symbol">(</a><a id="7967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a> <a id="7969" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a><a id="7972" class="Symbol">)</a> <a id="7974" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a>
  <a id="7980" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="7988" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7992" class="Symbol">((</a><a id="7994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a> <a id="7996" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a><a id="7999" class="Symbol">)</a> <a id="8001" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a><a id="8004" class="Symbol">)</a>
  <a id="8008" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="8011" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="8016" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8020" class="Symbol">(</a><a id="8021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="8029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a> <a id="8031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a> <a id="8033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a><a id="8034" class="Symbol">)</a> <a id="8036" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="8042" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8046" class="Symbol">(</a><a id="8047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a> <a id="8049" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8051" class="Symbol">(</a><a id="8052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a> <a id="8054" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a><a id="8057" class="Symbol">))</a>
  <a id="8062" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="8070" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7915" class="Bound">m</a> <a id="8076" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8078" class="Symbol">(</a><a id="8079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7918" class="Bound">n</a> <a id="8081" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7920" class="Bound">p</a><a id="8084" class="Symbol">)</a>
  <a id="8088" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p`
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well-founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.

## Induction as recursion

As a concrete example of how induction corresponds to recursion, here
is the computation that occurs when instantiating `m` to `2` in the
proof of associativity.

<pre class="Agda">{% raw %}<a id="+-assoc-2"></a><a id="11128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11128" class="Function">+-assoc-2</a> <a id="11138" class="Symbol">:</a> <a id="11140" class="Symbol">∀</a> <a id="11142" class="Symbol">(</a><a id="11143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11143" class="Bound">n</a> <a id="11145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11145" class="Bound">p</a> <a id="11147" class="Symbol">:</a> <a id="11149" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11150" class="Symbol">)</a> <a id="11152" class="Symbol">→</a> <a id="11154" class="Symbol">(</a><a id="11155" class="Number">2</a> <a id="11157" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11143" class="Bound">n</a><a id="11160" class="Symbol">)</a> <a id="11162" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11145" class="Bound">p</a> <a id="11166" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11168" class="Number">2</a> <a id="11170" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11172" class="Symbol">(</a><a id="11173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11143" class="Bound">n</a> <a id="11175" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11145" class="Bound">p</a><a id="11178" class="Symbol">)</a>
<a id="11180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11128" class="Function">+-assoc-2</a> <a id="11190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a> <a id="11192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a> <a id="11194" class="Symbol">=</a>
  <a id="11198" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="11208" class="Symbol">(</a><a id="11209" class="Number">2</a> <a id="11211" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a><a id="11214" class="Symbol">)</a> <a id="11216" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a>
  <a id="11222" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11230" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11234" class="Symbol">(</a><a id="11235" class="Number">1</a> <a id="11237" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a><a id="11240" class="Symbol">)</a> <a id="11242" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a>
  <a id="11248" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11256" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11260" class="Symbol">((</a><a id="11262" class="Number">1</a> <a id="11264" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a><a id="11267" class="Symbol">)</a> <a id="11269" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a><a id="11272" class="Symbol">)</a>
  <a id="11276" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="11279" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="11284" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11288" class="Symbol">(</a><a id="11289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11364" class="Function">+-assoc-1</a> <a id="11299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a> <a id="11301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a><a id="11302" class="Symbol">)</a> <a id="11304" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="11310" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11314" class="Symbol">(</a><a id="11315" class="Number">1</a> <a id="11317" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11319" class="Symbol">(</a><a id="11320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a> <a id="11322" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11324" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a><a id="11325" class="Symbol">))</a>
  <a id="11330" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="11338" class="Number">2</a> <a id="11340" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11342" class="Symbol">(</a><a id="11343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11190" class="Bound">n</a> <a id="11345" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11192" class="Bound">p</a><a id="11348" class="Symbol">)</a>
  <a id="11352" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
  <a id="11356" class="Keyword">where</a>
  <a id="11364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11364" class="Function">+-assoc-1</a> <a id="11374" class="Symbol">:</a> <a id="11376" class="Symbol">∀</a> <a id="11378" class="Symbol">(</a><a id="11379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11379" class="Bound">n</a> <a id="11381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11381" class="Bound">p</a> <a id="11383" class="Symbol">:</a> <a id="11385" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11386" class="Symbol">)</a> <a id="11388" class="Symbol">→</a> <a id="11390" class="Symbol">(</a><a id="11391" class="Number">1</a> <a id="11393" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11379" class="Bound">n</a><a id="11396" class="Symbol">)</a> <a id="11398" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11381" class="Bound">p</a> <a id="11402" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11404" class="Number">1</a> <a id="11406" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11408" class="Symbol">(</a><a id="11409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11379" class="Bound">n</a> <a id="11411" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11381" class="Bound">p</a><a id="11414" class="Symbol">)</a>
  <a id="11418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11364" class="Function">+-assoc-1</a> <a id="11428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a> <a id="11430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a> <a id="11432" class="Symbol">=</a>
    <a id="11438" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
      <a id="11450" class="Symbol">(</a><a id="11451" class="Number">1</a> <a id="11453" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a><a id="11456" class="Symbol">)</a> <a id="11458" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a>
    <a id="11466" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
      <a id="11476" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11480" class="Symbol">(</a><a id="11481" class="Number">0</a> <a id="11483" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a><a id="11486" class="Symbol">)</a> <a id="11488" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a>
    <a id="11496" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
      <a id="11506" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11510" class="Symbol">((</a><a id="11512" class="Number">0</a> <a id="11514" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a><a id="11517" class="Symbol">)</a> <a id="11519" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11521" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a><a id="11522" class="Symbol">)</a>
    <a id="11528" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="11531" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="11536" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11540" class="Symbol">(</a><a id="11541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11628" class="Function">+-assoc-0</a> <a id="11551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a> <a id="11553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a><a id="11554" class="Symbol">)</a> <a id="11556" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
      <a id="11564" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11568" class="Symbol">(</a><a id="11569" class="Number">0</a> <a id="11571" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11573" class="Symbol">(</a><a id="11574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a> <a id="11576" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a><a id="11579" class="Symbol">))</a>
    <a id="11586" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
      <a id="11596" class="Number">1</a> <a id="11598" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11600" class="Symbol">(</a><a id="11601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11428" class="Bound">n</a> <a id="11603" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11430" class="Bound">p</a><a id="11606" class="Symbol">)</a>
    <a id="11612" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
    <a id="11618" class="Keyword">where</a>
    <a id="11628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11628" class="Function">+-assoc-0</a> <a id="11638" class="Symbol">:</a> <a id="11640" class="Symbol">∀</a> <a id="11642" class="Symbol">(</a><a id="11643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11643" class="Bound">n</a> <a id="11645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11645" class="Bound">p</a> <a id="11647" class="Symbol">:</a> <a id="11649" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11650" class="Symbol">)</a> <a id="11652" class="Symbol">→</a> <a id="11654" class="Symbol">(</a><a id="11655" class="Number">0</a> <a id="11657" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11643" class="Bound">n</a><a id="11660" class="Symbol">)</a> <a id="11662" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11645" class="Bound">p</a> <a id="11666" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11668" class="Number">0</a> <a id="11670" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11672" class="Symbol">(</a><a id="11673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11643" class="Bound">n</a> <a id="11675" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11645" class="Bound">p</a><a id="11678" class="Symbol">)</a>
    <a id="11684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11628" class="Function">+-assoc-0</a> <a id="11694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11694" class="Bound">n</a> <a id="11696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11696" class="Bound">p</a> <a id="11698" class="Symbol">=</a>
      <a id="11706" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
        <a id="11720" class="Symbol">(</a><a id="11721" class="Number">0</a> <a id="11723" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11694" class="Bound">n</a><a id="11726" class="Symbol">)</a> <a id="11728" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11696" class="Bound">p</a>
      <a id="11738" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
        <a id="11750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11694" class="Bound">n</a> <a id="11752" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11696" class="Bound">p</a>
      <a id="11762" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
        <a id="11774" class="Number">0</a> <a id="11776" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11778" class="Symbol">(</a><a id="11779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11694" class="Bound">n</a> <a id="11781" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11696" class="Bound">p</a><a id="11784" class="Symbol">)</a>
      <a id="11792" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>


## Terminology and notation

The symbol `∀` appears in the statement of associativity to indicate that
it holds for all numbers `m`, `n`, and `p`.  We refer to `∀` as the _universal
quantifier_, and it is discussed further in Chapter [Quantifiers]({{ site.baseurl }}{% link out/plfa/Quantifiers.md%}).

Evidence for a universal quantifier is a function.  The notations

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

and

    +-assoc : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → (m + n) + p ≡ m + (n + p)

are equivalent. They differ from a function type such as `ℕ → ℕ → ℕ`
in that variables are associated with the each argument type, and the
result type may mention (or depend upon) these variables; hence they
are called _dependent functions_.


## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof:
<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="13017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13017" class="Function">+-identityʳ</a> <a id="13029" class="Symbol">:</a> <a id="13031" class="Symbol">∀</a> <a id="13033" class="Symbol">(</a><a id="13034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13034" class="Bound">m</a> <a id="13036" class="Symbol">:</a> <a id="13038" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13039" class="Symbol">)</a> <a id="13041" class="Symbol">→</a> <a id="13043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13034" class="Bound">m</a> <a id="13045" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13047" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13052" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13034" class="Bound">m</a>
<a id="13056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13017" class="Function">+-identityʳ</a> <a id="13068" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13073" class="Symbol">=</a>
  <a id="13077" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="13087" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13092" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13094" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="13101" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="13109" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="13116" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="13118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13017" class="Function">+-identityʳ</a> <a id="13130" class="Symbol">(</a><a id="13131" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13135" class="Bound">m</a><a id="13136" class="Symbol">)</a> <a id="13138" class="Symbol">=</a>
  <a id="13142" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="13152" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13135" class="Bound">m</a> <a id="13158" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13160" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="13167" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="13175" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13179" class="Symbol">(</a><a id="13180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13135" class="Bound">m</a> <a id="13182" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13184" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="13188" class="Symbol">)</a>
  <a id="13192" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="13195" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="13200" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13204" class="Symbol">(</a><a id="13205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13017" class="Function">+-identityʳ</a> <a id="13217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13135" class="Bound">m</a><a id="13218" class="Symbol">)</a> <a id="13220" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="13226" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13135" class="Bound">m</a>
  <a id="13234" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof:
<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="14690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14690" class="Function">+-suc</a> <a id="14696" class="Symbol">:</a> <a id="14698" class="Symbol">∀</a> <a id="14700" class="Symbol">(</a><a id="14701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14701" class="Bound">m</a> <a id="14703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14703" class="Bound">n</a> <a id="14705" class="Symbol">:</a> <a id="14707" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14708" class="Symbol">)</a> <a id="14710" class="Symbol">→</a> <a id="14712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14701" class="Bound">m</a> <a id="14714" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14716" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14703" class="Bound">n</a> <a id="14722" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="14724" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14728" class="Symbol">(</a><a id="14729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14701" class="Bound">m</a> <a id="14731" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14703" class="Bound">n</a><a id="14734" class="Symbol">)</a>
<a id="14736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14690" class="Function">+-suc</a> <a id="14742" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14747" class="Bound">n</a> <a id="14749" class="Symbol">=</a>
  <a id="14753" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="14763" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14768" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14770" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14747" class="Bound">n</a>
  <a id="14778" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="14786" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14747" class="Bound">n</a>
  <a id="14794" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="14802" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14806" class="Symbol">(</a><a id="14807" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14812" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14747" class="Bound">n</a><a id="14815" class="Symbol">)</a>
  <a id="14819" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="14821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14690" class="Function">+-suc</a> <a id="14827" class="Symbol">(</a><a id="14828" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14832" class="Bound">m</a><a id="14833" class="Symbol">)</a> <a id="14835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14835" class="Bound">n</a> <a id="14837" class="Symbol">=</a>
  <a id="14841" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="14851" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14832" class="Bound">m</a> <a id="14857" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14859" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14835" class="Bound">n</a>
  <a id="14867" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="14875" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14879" class="Symbol">(</a><a id="14880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14832" class="Bound">m</a> <a id="14882" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14884" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14835" class="Bound">n</a><a id="14889" class="Symbol">)</a>
  <a id="14893" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="14896" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="14901" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14905" class="Symbol">(</a><a id="14906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14690" class="Function">+-suc</a> <a id="14912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14832" class="Bound">m</a> <a id="14914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14835" class="Bound">n</a><a id="14915" class="Symbol">)</a> <a id="14917" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="14923" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14927" class="Symbol">(</a><a id="14928" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14932" class="Symbol">(</a><a id="14933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14832" class="Bound">m</a> <a id="14935" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14835" class="Bound">n</a><a id="14938" class="Symbol">))</a>
  <a id="14943" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="14951" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14955" class="Symbol">(</a><a id="14956" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14832" class="Bound">m</a> <a id="14962" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14835" class="Bound">n</a><a id="14965" class="Symbol">)</a>
  <a id="14969" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof:
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="16279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16279" class="Function">+-comm</a> <a id="16286" class="Symbol">:</a> <a id="16288" class="Symbol">∀</a> <a id="16290" class="Symbol">(</a><a id="16291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16291" class="Bound">m</a> <a id="16293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16293" class="Bound">n</a> <a id="16295" class="Symbol">:</a> <a id="16297" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16298" class="Symbol">)</a> <a id="16300" class="Symbol">→</a> <a id="16302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16291" class="Bound">m</a> <a id="16304" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16293" class="Bound">n</a> <a id="16308" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16293" class="Bound">n</a> <a id="16312" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16291" class="Bound">m</a>
<a id="16316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16279" class="Function">+-comm</a> <a id="16323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16323" class="Bound">m</a> <a id="16325" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16330" class="Symbol">=</a>
  <a id="16334" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="16344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16323" class="Bound">m</a> <a id="16346" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16348" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="16355" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="16358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13017" class="Function">+-identityʳ</a> <a id="16370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16323" class="Bound">m</a> <a id="16372" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="16378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16323" class="Bound">m</a>
  <a id="16382" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="16390" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16395" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16323" class="Bound">m</a>
  <a id="16401" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>
<a id="16403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16279" class="Function">+-comm</a> <a id="16410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a> <a id="16412" class="Symbol">(</a><a id="16413" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a><a id="16418" class="Symbol">)</a> <a id="16420" class="Symbol">=</a>
  <a id="16424" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="16434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a> <a id="16436" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16438" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a>
  <a id="16446" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="16449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14690" class="Function">+-suc</a> <a id="16455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a> <a id="16457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a> <a id="16459" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="16465" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16469" class="Symbol">(</a><a id="16470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a> <a id="16472" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a><a id="16475" class="Symbol">)</a>
  <a id="16479" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="16482" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="16487" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16491" class="Symbol">(</a><a id="16492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16279" class="Function">+-comm</a> <a id="16499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a> <a id="16501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a><a id="16502" class="Symbol">)</a> <a id="16504" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="16510" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16514" class="Symbol">(</a><a id="16515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a> <a id="16517" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a><a id="16520" class="Symbol">)</a>
  <a id="16524" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4134" class="Function Operator">≡⟨⟩</a>
    <a id="16532" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16417" class="Bound">n</a> <a id="16538" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16410" class="Bound">m</a>
  <a id="16544" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like.
Here is an example:
<pre class="Agda">{% raw %}<a id="+-rearrange"></a><a id="18106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18106" class="Function">+-rearrange</a> <a id="18118" class="Symbol">:</a> <a id="18120" class="Symbol">∀</a> <a id="18122" class="Symbol">(</a><a id="18123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18123" class="Bound">m</a> <a id="18125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18125" class="Bound">n</a> <a id="18127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18127" class="Bound">p</a> <a id="18129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18129" class="Bound">q</a> <a id="18131" class="Symbol">:</a> <a id="18133" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18134" class="Symbol">)</a> <a id="18136" class="Symbol">→</a> <a id="18138" class="Symbol">(</a><a id="18139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18123" class="Bound">m</a> <a id="18141" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18125" class="Bound">n</a><a id="18144" class="Symbol">)</a> <a id="18146" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18148" class="Symbol">(</a><a id="18149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18127" class="Bound">p</a> <a id="18151" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18129" class="Bound">q</a><a id="18154" class="Symbol">)</a> <a id="18156" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18123" class="Bound">m</a> <a id="18160" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18162" class="Symbol">(</a><a id="18163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18125" class="Bound">n</a> <a id="18165" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18127" class="Bound">p</a><a id="18168" class="Symbol">)</a> <a id="18170" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18129" class="Bound">q</a>
<a id="18174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18106" class="Function">+-rearrange</a> <a id="18186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a> <a id="18192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a> <a id="18194" class="Symbol">=</a>
  <a id="18198" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4076" class="Function Operator">begin</a>
    <a id="18208" class="Symbol">(</a><a id="18209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18211" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a><a id="18214" class="Symbol">)</a> <a id="18216" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18218" class="Symbol">(</a><a id="18219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a> <a id="18221" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a><a id="18224" class="Symbol">)</a>
  <a id="18228" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="18231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="18239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18243" class="Symbol">(</a><a id="18244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a> <a id="18246" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a><a id="18249" class="Symbol">)</a> <a id="18251" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="18257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18259" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18261" class="Symbol">(</a><a id="18262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18264" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18266" class="Symbol">(</a><a id="18267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a> <a id="18269" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a><a id="18272" class="Symbol">))</a>
  <a id="18277" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="18280" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="18285" class="Symbol">(</a><a id="18286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18288" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+_</a><a id="18290" class="Symbol">)</a> <a id="18292" class="Symbol">(</a><a id="18293" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="18297" class="Symbol">(</a><a id="18298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="18306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a> <a id="18310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a><a id="18311" class="Symbol">))</a> <a id="18314" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="18320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18322" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18324" class="Symbol">((</a><a id="18326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18328" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a><a id="18331" class="Symbol">)</a> <a id="18333" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a><a id="18336" class="Symbol">)</a>
  <a id="18340" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">≡⟨</a> <a id="18343" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="18347" class="Symbol">(</a><a id="18348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7760" class="Function">+-assoc</a> <a id="18356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18358" class="Symbol">(</a><a id="18359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18361" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a><a id="18364" class="Symbol">)</a> <a id="18366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a><a id="18367" class="Symbol">)</a> <a id="18369" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4193" class="Function Operator">⟩</a>
    <a id="18375" class="Symbol">(</a><a id="18376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18186" class="Bound">m</a> <a id="18378" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18380" class="Symbol">(</a><a id="18381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18188" class="Bound">n</a> <a id="18383" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18190" class="Bound">p</a><a id="18386" class="Symbol">))</a> <a id="18389" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18192" class="Bound">q</a>
  <a id="18395" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#4374" class="Function Operator">∎</a>{% endraw %}</pre>
No induction is required, we simply apply associativity twice.
A few points are worthy of note.

First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.

Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:

    (n + p) + q ≡ n + (p + q)

To shift them the other way, we use `sym (+-assoc n p q)`:

    n + (p + q) ≡ (n + p) + q

In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.

Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into:

    m + (n + (p + q)) ≡ m + ((n + p) + q)

Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgments asserting associativity:

     -- In the beginning, we know nothing about associativity.

Now, we apply the rules to all the judgments we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments:

    -- On the first day, we know about associativity of 0.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgments from the day before, plus any judgments added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgments:

    -- On the second day, we know about associativity of 0 and 1.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again:

    -- On the third day, we know about associativity of 0, 1, and 2.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now:

    -- On the fourth day, we know about associativity of 0, 1, 2, and 3.
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgments where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#finite-creation).

<pre class="Agda">{% raw %}<a id="21814" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations:
<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="22046" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22046" class="Function">+-assoc′</a> <a id="22055" class="Symbol">:</a> <a id="22057" class="Symbol">∀</a> <a id="22059" class="Symbol">(</a><a id="22060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22060" class="Bound">m</a> <a id="22062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22062" class="Bound">n</a> <a id="22064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22064" class="Bound">p</a> <a id="22066" class="Symbol">:</a> <a id="22068" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22069" class="Symbol">)</a> <a id="22071" class="Symbol">→</a> <a id="22073" class="Symbol">(</a><a id="22074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22060" class="Bound">m</a> <a id="22076" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22062" class="Bound">n</a><a id="22079" class="Symbol">)</a> <a id="22081" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22064" class="Bound">p</a> <a id="22085" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="22087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22060" class="Bound">m</a> <a id="22089" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22091" class="Symbol">(</a><a id="22092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22062" class="Bound">n</a> <a id="22094" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22064" class="Bound">p</a><a id="22097" class="Symbol">)</a>
<a id="22099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22046" class="Function">+-assoc′</a> <a id="22108" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="22116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22116" class="Bound">n</a> <a id="22118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22118" class="Bound">p</a>                          <a id="22145" class="Symbol">=</a>  <a id="22148" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="22153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22046" class="Function">+-assoc′</a> <a id="22162" class="Symbol">(</a><a id="22163" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="22167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22167" class="Bound">m</a><a id="22168" class="Symbol">)</a> <a id="22170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22170" class="Bound">n</a> <a id="22172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22172" class="Bound">p</a>  <a id="22175" class="Keyword">rewrite</a> <a id="22183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22046" class="Function">+-assoc′</a> <a id="22192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22167" class="Bound">m</a> <a id="22194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22170" class="Bound">n</a> <a id="22196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#22172" class="Bound">p</a>  <a id="22199" class="Symbol">=</a>  <a id="22202" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations:
<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="23121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23121" class="Function">+-identity′</a> <a id="23133" class="Symbol">:</a> <a id="23135" class="Symbol">∀</a> <a id="23137" class="Symbol">(</a><a id="23138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23138" class="Bound">n</a> <a id="23140" class="Symbol">:</a> <a id="23142" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="23143" class="Symbol">)</a> <a id="23145" class="Symbol">→</a> <a id="23147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23138" class="Bound">n</a> <a id="23149" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23151" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="23156" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="23158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23138" class="Bound">n</a>
<a id="23160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23121" class="Function">+-identity′</a> <a id="23172" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="23177" class="Symbol">=</a> <a id="23179" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="23184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23121" class="Function">+-identity′</a> <a id="23196" class="Symbol">(</a><a id="23197" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">n</a><a id="23202" class="Symbol">)</a> <a id="23204" class="Keyword">rewrite</a> <a id="23212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23121" class="Function">+-identity′</a> <a id="23224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23201" class="Bound">n</a> <a id="23226" class="Symbol">=</a> <a id="23228" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="23234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23234" class="Function">+-suc′</a> <a id="23241" class="Symbol">:</a> <a id="23243" class="Symbol">∀</a> <a id="23245" class="Symbol">(</a><a id="23246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23246" class="Bound">m</a> <a id="23248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23248" class="Bound">n</a> <a id="23250" class="Symbol">:</a> <a id="23252" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="23253" class="Symbol">)</a> <a id="23255" class="Symbol">→</a> <a id="23257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23246" class="Bound">m</a> <a id="23259" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23261" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23248" class="Bound">n</a> <a id="23267" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="23269" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23273" class="Symbol">(</a><a id="23274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23246" class="Bound">m</a> <a id="23276" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23248" class="Bound">n</a><a id="23279" class="Symbol">)</a>
<a id="23281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23234" class="Function">+-suc′</a> <a id="23288" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="23293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23293" class="Bound">n</a> <a id="23295" class="Symbol">=</a> <a id="23297" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="23302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23234" class="Function">+-suc′</a> <a id="23309" class="Symbol">(</a><a id="23310" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23314" class="Bound">m</a><a id="23315" class="Symbol">)</a> <a id="23317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23317" class="Bound">n</a> <a id="23319" class="Keyword">rewrite</a> <a id="23327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23234" class="Function">+-suc′</a> <a id="23334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23314" class="Bound">m</a> <a id="23336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23317" class="Bound">n</a> <a id="23338" class="Symbol">=</a> <a id="23340" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="23346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23346" class="Function">+-comm′</a> <a id="23354" class="Symbol">:</a> <a id="23356" class="Symbol">∀</a> <a id="23358" class="Symbol">(</a><a id="23359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23359" class="Bound">m</a> <a id="23361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23361" class="Bound">n</a> <a id="23363" class="Symbol">:</a> <a id="23365" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="23366" class="Symbol">)</a> <a id="23368" class="Symbol">→</a> <a id="23370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23359" class="Bound">m</a> <a id="23372" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23361" class="Bound">n</a> <a id="23376" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="23378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23361" class="Bound">n</a> <a id="23380" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="23382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23359" class="Bound">m</a>
<a id="23384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23346" class="Function">+-comm′</a> <a id="23392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23392" class="Bound">m</a> <a id="23394" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="23399" class="Keyword">rewrite</a> <a id="23407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23121" class="Function">+-identity′</a> <a id="23419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23392" class="Bound">m</a> <a id="23421" class="Symbol">=</a> <a id="23423" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="23428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23346" class="Function">+-comm′</a> <a id="23436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23436" class="Bound">m</a> <a id="23438" class="Symbol">(</a><a id="23439" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="23443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23443" class="Bound">n</a><a id="23444" class="Symbol">)</a> <a id="23446" class="Keyword">rewrite</a> <a id="23454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23234" class="Function">+-suc′</a> <a id="23461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23436" class="Bound">m</a> <a id="23463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23443" class="Bound">n</a> <a id="23465" class="Symbol">|</a> <a id="23467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23346" class="Function">+-comm′</a> <a id="23475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23436" class="Bound">m</a> <a id="23477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#23443" class="Bound">n</a> <a id="23479" class="Symbol">=</a> <a id="23481" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text:

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgment.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

<pre class="Agda">{% raw %}<a id="27037" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

<pre class="Agda">{% raw %}<a id="27278" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

<pre class="Agda">{% raw %}<a id="27495" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

<pre class="Agda">{% raw %}<a id="27768" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

<pre class="Agda">{% raw %}<a id="27938" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

<pre class="Agda">{% raw %}<a id="28152" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


#### Exercise `+*^` (stretch)

Show the following three laws

    m ^ (n + p) ≡ (m ^ n) * (m ^ p)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)
    m ^ (n * p) ≡ (m ^ n) ^ p

for all `m`, `n`, and `p`.


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype of bitstrings representing natural numbers
<pre class="Agda">{% raw %}<a id="28551" class="Keyword">data</a> <a id="Bin"></a><a id="28556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28556" class="Datatype">Bin</a> <a id="28560" class="Symbol">:</a> <a id="28562" class="PrimitiveType">Set</a> <a id="28566" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="28574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28574" class="InductiveConstructor">nil</a> <a id="28578" class="Symbol">:</a> <a id="28580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28556" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="28586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28586" class="InductiveConstructor Operator">x0_</a> <a id="28590" class="Symbol">:</a> <a id="28592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28556" class="Datatype">Bin</a> <a id="28596" class="Symbol">→</a> <a id="28598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28556" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="28604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28604" class="InductiveConstructor Operator">x1_</a> <a id="28608" class="Symbol">:</a> <a id="28610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28556" class="Datatype">Bin</a> <a id="28614" class="Symbol">→</a> <a id="28616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#28556" class="Datatype">Bin</a>{% endraw %}</pre>
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings:

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

<pre class="Agda">{% raw %}<a id="28966" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda">{% raw %}<a id="29119" class="Keyword">import</a> <a id="29126" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="29146" class="Keyword">using</a> <a id="29152" class="Symbol">(</a><a id="29153" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9375" class="Function">+-assoc</a><a id="29160" class="Symbol">;</a> <a id="29162" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9531" class="Function">+-identityʳ</a><a id="29173" class="Symbol">;</a> <a id="29175" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9272" class="Function">+-suc</a><a id="29180" class="Symbol">;</a> <a id="29182" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="29188" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode:

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
