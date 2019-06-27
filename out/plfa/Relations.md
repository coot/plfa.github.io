---
src       : src/plfa/Relations.lagda
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

<pre class="Agda">{% raw %}<a id="170" class="Keyword">module</a> <a id="177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda">{% raw %}<a id="373" class="Keyword">import</a> <a id="380" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="418" class="Symbol">as</a> <a id="421" class="Module">Eq</a>
<a id="424" class="Keyword">open</a> <a id="429" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a><a id="439" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="442" class="Symbol">;</a> <a id="444" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="448" class="Symbol">;</a> <a id="450" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="454" class="Symbol">)</a>
<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="477" class="Keyword">using</a> <a id="483" class="Symbol">(</a><a id="484" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="485" class="Symbol">;</a> <a id="487" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="491" class="Symbol">;</a> <a id="493" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="496" class="Symbol">;</a> <a id="498" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="501" class="Symbol">)</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="535" class="Keyword">using</a> <a id="541" class="Symbol">(</a><a id="542" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="548" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1225" class="Keyword">data</a> <a id="_≤_"></a><a id="1230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">_≤_</a> <a id="1234" class="Symbol">:</a> <a id="1236" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1238" class="Symbol">→</a> <a id="1240" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1242" class="Symbol">→</a> <a id="1244" class="PrimitiveType">Set</a> <a id="1248" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="1261" class="Symbol">:</a> <a id="1263" class="Symbol">∀</a> <a id="1265" class="Symbol">{</a><a id="1266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1266" class="Bound">n</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1271" class="Symbol">}</a>
      <a id="1279" class="Comment">--------</a>
    <a id="1292" class="Symbol">→</a> <a id="1294" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1266" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="1310" class="Symbol">:</a> <a id="1312" class="Symbol">∀</a> <a id="1314" class="Symbol">{</a><a id="1315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1322" class="Symbol">}</a>
    <a id="1328" class="Symbol">→</a> <a id="1330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a>
      <a id="1342" class="Comment">-------------</a>
    <a id="1360" class="Symbol">→</a> <a id="1362" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1370" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
<pre class="Agda">{% raw %}<a id="2652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2652" class="Function">_</a> <a id="2654" class="Symbol">:</a> <a id="2656" class="Number">2</a> <a id="2658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="2660" class="Number">4</a>
<a id="2662" class="Symbol">_</a> <a id="2664" class="Symbol">=</a> <a id="2666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="2670" class="Symbol">(</a><a id="2671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="2675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a><a id="2678" class="Symbol">)</a>{% endraw %}</pre>




## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
<pre class="Agda">{% raw %}<a id="3673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3673" class="Function">_</a> <a id="3675" class="Symbol">:</a> <a id="3677" class="Number">2</a> <a id="3679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3681" class="Number">4</a>
<a id="3683" class="Symbol">_</a> <a id="3685" class="Symbol">=</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3691" class="Symbol">{</a><a id="3692" class="Number">1</a><a id="3693" class="Symbol">}</a> <a id="3695" class="Symbol">{</a><a id="3696" class="Number">3</a><a id="3697" class="Symbol">}</a> <a id="3699" class="Symbol">(</a><a id="3700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3704" class="Symbol">{</a><a id="3705" class="Number">0</a><a id="3706" class="Symbol">}</a> <a id="3708" class="Symbol">{</a><a id="3709" class="Number">2</a><a id="3710" class="Symbol">}</a> <a id="3712" class="Symbol">(</a><a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="3717" class="Symbol">{</a><a id="3718" class="Number">2</a><a id="3719" class="Symbol">}))</a>{% endraw %}</pre>
One may also identify implicit arguments by name:
<pre class="Agda">{% raw %}<a id="3797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3797" class="Function">_</a> <a id="3799" class="Symbol">:</a> <a id="3801" class="Number">2</a> <a id="3803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3805" class="Number">4</a>
<a id="3807" class="Symbol">_</a> <a id="3809" class="Symbol">=</a> <a id="3811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3815" class="Symbol">{</a><a id="3816" class="Argument">m</a> <a id="3818" class="Symbol">=</a> <a id="3820" class="Number">1</a><a id="3821" class="Symbol">}</a> <a id="3823" class="Symbol">{</a><a id="3824" class="Argument">n</a> <a id="3826" class="Symbol">=</a> <a id="3828" class="Number">3</a><a id="3829" class="Symbol">}</a> <a id="3831" class="Symbol">(</a><a id="3832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3836" class="Symbol">{</a><a id="3837" class="Argument">m</a> <a id="3839" class="Symbol">=</a> <a id="3841" class="Number">0</a><a id="3842" class="Symbol">}</a> <a id="3844" class="Symbol">{</a><a id="3845" class="Argument">n</a> <a id="3847" class="Symbol">=</a> <a id="3849" class="Number">2</a><a id="3850" class="Symbol">}</a> <a id="3852" class="Symbol">(</a><a id="3853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="3857" class="Symbol">{</a><a id="3858" class="Argument">n</a> <a id="3860" class="Symbol">=</a> <a id="3862" class="Number">2</a><a id="3863" class="Symbol">}))</a>{% endraw %}</pre>
In the latter format, you may only supply some implicit arguments:
<pre class="Agda">{% raw %}<a id="3958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3958" class="Function">_</a> <a id="3960" class="Symbol">:</a> <a id="3962" class="Number">2</a> <a id="3964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3966" class="Number">4</a>
<a id="3968" class="Symbol">_</a> <a id="3970" class="Symbol">=</a> <a id="3972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3976" class="Symbol">{</a><a id="3977" class="Argument">n</a> <a id="3979" class="Symbol">=</a> <a id="3981" class="Number">3</a><a id="3982" class="Symbol">}</a> <a id="3984" class="Symbol">(</a><a id="3985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3989" class="Symbol">{</a><a id="3990" class="Argument">n</a> <a id="3992" class="Symbol">=</a> <a id="3994" class="Number">2</a><a id="3995" class="Symbol">}</a> <a id="3997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a><a id="4000" class="Symbol">)</a>{% endraw %}</pre>
It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
<pre class="Agda">{% raw %}<a id="4161" class="Keyword">infix</a> <a id="4167" class="Number">4</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}).


## Inversion

In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
<pre class="Agda">{% raw %}<a id="inv-s≤s"></a><a id="5187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5187" class="Function">inv-s≤s</a> <a id="5195" class="Symbol">:</a> <a id="5197" class="Symbol">∀</a> <a id="5199" class="Symbol">{</a><a id="5200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5200" class="Bound">m</a> <a id="5202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5202" class="Bound">n</a> <a id="5204" class="Symbol">:</a> <a id="5206" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5207" class="Symbol">}</a>
  <a id="5211" class="Symbol">→</a> <a id="5213" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5200" class="Bound">m</a> <a id="5219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="5221" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5202" class="Bound">n</a>
    <a id="5231" class="Comment">-------------</a>
  <a id="5247" class="Symbol">→</a> <a id="5249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5200" class="Bound">m</a> <a id="5251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="5253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5202" class="Bound">n</a>
<a id="5255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5187" class="Function">inv-s≤s</a> <a id="5263" class="Symbol">(</a><a id="5264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="5268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5268" class="Bound">m≤n</a><a id="5271" class="Symbol">)</a> <a id="5273" class="Symbol">=</a> <a id="5275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5268" class="Bound">m≤n</a>{% endraw %}</pre>
Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
<pre class="Agda">{% raw %}<a id="inv-z≤n"></a><a id="5575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5575" class="Function">inv-z≤n</a> <a id="5583" class="Symbol">:</a> <a id="5585" class="Symbol">∀</a> <a id="5587" class="Symbol">{</a><a id="5588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5588" class="Bound">m</a> <a id="5590" class="Symbol">:</a> <a id="5592" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5593" class="Symbol">}</a>
  <a id="5597" class="Symbol">→</a> <a id="5599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5588" class="Bound">m</a> <a id="5601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="5603" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
    <a id="5612" class="Comment">--------</a>
  <a id="5623" class="Symbol">→</a> <a id="5625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5588" class="Bound">m</a> <a id="5627" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5629" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
<a id="5634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5575" class="Function">inv-z≤n</a> <a id="5642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="5646" class="Symbol">=</a> <a id="5648" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

<pre class="Agda">{% raw %}<a id="7155" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

Give an example of a partial order that is not a total order.

<pre class="Agda">{% raw %}<a id="7266" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="7582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a> <a id="7589" class="Symbol">:</a> <a id="7591" class="Symbol">∀</a> <a id="7593" class="Symbol">{</a><a id="7594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7594" class="Bound">n</a> <a id="7596" class="Symbol">:</a> <a id="7598" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7599" class="Symbol">}</a>
    <a id="7605" class="Comment">-----</a>
  <a id="7613" class="Symbol">→</a> <a id="7615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7594" class="Bound">n</a> <a id="7617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="7619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7594" class="Bound">n</a>
<a id="7621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a> <a id="7628" class="Symbol">{</a><a id="7629" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="7633" class="Symbol">}</a> <a id="7635" class="Symbol">=</a> <a id="7637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="7641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a> <a id="7648" class="Symbol">{</a><a id="7649" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7653" class="Bound">n</a><a id="7654" class="Symbol">}</a> <a id="7656" class="Symbol">=</a> <a id="7658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="7662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a>{% endraw %}</pre>
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="8315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8323" class="Symbol">:</a> <a id="8325" class="Symbol">∀</a> <a id="8327" class="Symbol">{</a><a id="8328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8328" class="Bound">m</a> <a id="8330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8330" class="Bound">n</a> <a id="8332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8332" class="Bound">p</a> <a id="8334" class="Symbol">:</a> <a id="8336" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8337" class="Symbol">}</a>
  <a id="8341" class="Symbol">→</a> <a id="8343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8328" class="Bound">m</a> <a id="8345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8330" class="Bound">n</a>
  <a id="8351" class="Symbol">→</a> <a id="8353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8330" class="Bound">n</a> <a id="8355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8332" class="Bound">p</a>
    <a id="8363" class="Comment">-----</a>
  <a id="8371" class="Symbol">→</a> <a id="8373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8328" class="Bound">m</a> <a id="8375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8332" class="Bound">p</a>
<a id="8379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="8397" class="Symbol">_</a>          <a id="8408" class="Symbol">=</a>  <a id="8411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="8415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8423" class="Symbol">(</a><a id="8424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8428" class="Bound">m≤n</a><a id="8431" class="Symbol">)</a> <a id="8433" class="Symbol">(</a><a id="8434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8438" class="Bound">n≤p</a><a id="8441" class="Symbol">)</a>  <a id="8444" class="Symbol">=</a>  <a id="8447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8451" class="Symbol">(</a><a id="8452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8428" class="Bound">m≤n</a> <a id="8464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8438" class="Bound">n≤p</a><a id="8467" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="9444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9453" class="Symbol">:</a> <a id="9455" class="Symbol">∀</a> <a id="9457" class="Symbol">(</a><a id="9458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9458" class="Bound">m</a> <a id="9460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9460" class="Bound">n</a> <a id="9462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9462" class="Bound">p</a> <a id="9464" class="Symbol">:</a> <a id="9466" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9467" class="Symbol">)</a>
  <a id="9471" class="Symbol">→</a> <a id="9473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9458" class="Bound">m</a> <a id="9475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9460" class="Bound">n</a>
  <a id="9481" class="Symbol">→</a> <a id="9483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9460" class="Bound">n</a> <a id="9485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9462" class="Bound">p</a>
    <a id="9493" class="Comment">-----</a>
  <a id="9501" class="Symbol">→</a> <a id="9503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9458" class="Bound">m</a> <a id="9505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9462" class="Bound">p</a>
<a id="9509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9518" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="9526" class="Symbol">_</a>       <a id="9534" class="Symbol">_</a>       <a id="9542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="9552" class="Symbol">_</a>          <a id="9563" class="Symbol">=</a>  <a id="9566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="9570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9579" class="Symbol">(</a><a id="9580" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9584" class="Bound">m</a><a id="9585" class="Symbol">)</a> <a id="9587" class="Symbol">(</a><a id="9588" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9592" class="Bound">n</a><a id="9593" class="Symbol">)</a> <a id="9595" class="Symbol">(</a><a id="9596" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9600" class="Bound">p</a><a id="9601" class="Symbol">)</a> <a id="9603" class="Symbol">(</a><a id="9604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m≤n</a><a id="9611" class="Symbol">)</a> <a id="9613" class="Symbol">(</a><a id="9614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9618" class="Bound">n≤p</a><a id="9621" class="Symbol">)</a>  <a id="9624" class="Symbol">=</a>  <a id="9627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9631" class="Symbol">(</a><a id="9632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9584" class="Bound">m</a> <a id="9643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9592" class="Bound">n</a> <a id="9645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9600" class="Bound">p</a> <a id="9647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m≤n</a> <a id="9651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9618" class="Bound">n≤p</a><a id="9654" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="10415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10415" class="Function">≤-antisym</a> <a id="10425" class="Symbol">:</a> <a id="10427" class="Symbol">∀</a> <a id="10429" class="Symbol">{</a><a id="10430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10430" class="Bound">m</a> <a id="10432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10432" class="Bound">n</a> <a id="10434" class="Symbol">:</a> <a id="10436" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10437" class="Symbol">}</a>
  <a id="10441" class="Symbol">→</a> <a id="10443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10430" class="Bound">m</a> <a id="10445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="10447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10432" class="Bound">n</a>
  <a id="10451" class="Symbol">→</a> <a id="10453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10432" class="Bound">n</a> <a id="10455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="10457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10430" class="Bound">m</a>
    <a id="10463" class="Comment">-----</a>
  <a id="10471" class="Symbol">→</a> <a id="10473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10430" class="Bound">m</a> <a id="10475" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="10477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10432" class="Bound">n</a>
<a id="10479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10415" class="Function">≤-antisym</a> <a id="10489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="10499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>        <a id="10510" class="Symbol">=</a>  <a id="10513" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="10518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10415" class="Function">≤-antisym</a> <a id="10528" class="Symbol">(</a><a id="10529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="10533" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10533" class="Bound">m≤n</a><a id="10536" class="Symbol">)</a> <a id="10538" class="Symbol">(</a><a id="10539" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="10543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10543" class="Bound">n≤m</a><a id="10546" class="Symbol">)</a>  <a id="10549" class="Symbol">=</a>  <a id="10552" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="10557" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10561" class="Symbol">(</a><a id="10562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10415" class="Function">≤-antisym</a> <a id="10572" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10533" class="Bound">m≤n</a> <a id="10576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10543" class="Bound">n≤m</a><a id="10579" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

<pre class="Agda">{% raw %}<a id="11390" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
<pre class="Agda">{% raw %}<a id="11660" class="Keyword">data</a> <a id="Total"></a><a id="11665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="11671" class="Symbol">(</a><a id="11672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11672" class="Bound">m</a> <a id="11674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">n</a> <a id="11676" class="Symbol">:</a> <a id="11678" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11679" class="Symbol">)</a> <a id="11681" class="Symbol">:</a> <a id="11683" class="PrimitiveType">Set</a> <a id="11687" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="11704" class="Symbol">:</a>
      <a id="11712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11672" class="Bound">m</a> <a id="11714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="11716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">n</a>
      <a id="11724" class="Comment">---------</a>
    <a id="11738" class="Symbol">→</a> <a id="11740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="11746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11672" class="Bound">m</a> <a id="11748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="11761" class="Symbol">:</a>
      <a id="11769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">n</a> <a id="11771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="11773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11672" class="Bound">m</a>
      <a id="11781" class="Comment">---------</a>
    <a id="11795" class="Symbol">→</a> <a id="11797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="11803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11672" class="Bound">m</a> <a id="11805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
<pre class="Agda">{% raw %}<a id="12295" class="Keyword">data</a> <a id="Total′"></a><a id="12300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12300" class="Datatype">Total′</a> <a id="12307" class="Symbol">:</a> <a id="12309" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="12311" class="Symbol">→</a> <a id="12313" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="12315" class="Symbol">→</a> <a id="12317" class="PrimitiveType">Set</a> <a id="12321" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12330" class="InductiveConstructor">forward′</a> <a id="12339" class="Symbol">:</a> <a id="12341" class="Symbol">∀</a> <a id="12343" class="Symbol">{</a><a id="12344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12344" class="Bound">m</a> <a id="12346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12346" class="Bound">n</a> <a id="12348" class="Symbol">:</a> <a id="12350" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12351" class="Symbol">}</a>
    <a id="12357" class="Symbol">→</a> <a id="12359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12344" class="Bound">m</a> <a id="12361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="12363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12346" class="Bound">n</a>
      <a id="12371" class="Comment">----------</a>
    <a id="12386" class="Symbol">→</a> <a id="12388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12300" class="Datatype">Total′</a> <a id="12395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12344" class="Bound">m</a> <a id="12397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12346" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12402" class="InductiveConstructor">flipped′</a> <a id="12411" class="Symbol">:</a> <a id="12413" class="Symbol">∀</a> <a id="12415" class="Symbol">{</a><a id="12416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12416" class="Bound">m</a> <a id="12418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12418" class="Bound">n</a> <a id="12420" class="Symbol">:</a> <a id="12422" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12423" class="Symbol">}</a>
    <a id="12429" class="Symbol">→</a> <a id="12431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12418" class="Bound">n</a> <a id="12433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="12435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12416" class="Bound">m</a>
      <a id="12443" class="Comment">----------</a>
    <a id="12458" class="Symbol">→</a> <a id="12460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12300" class="Datatype">Total′</a> <a id="12467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12416" class="Bound">m</a> <a id="12469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12418" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="13004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13004" class="Function">≤-total</a> <a id="13012" class="Symbol">:</a> <a id="13014" class="Symbol">∀</a> <a id="13016" class="Symbol">(</a><a id="13017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13017" class="Bound">m</a> <a id="13019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13019" class="Bound">n</a> <a id="13021" class="Symbol">:</a> <a id="13023" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13024" class="Symbol">)</a> <a id="13026" class="Symbol">→</a> <a id="13028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="13034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13017" class="Bound">m</a> <a id="13036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13019" class="Bound">n</a>
<a id="13038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13004" class="Function">≤-total</a> <a id="13046" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13054" class="Bound">n</a>                         <a id="13080" class="Symbol">=</a>  <a id="13083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="13091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="13095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13004" class="Function">≤-total</a> <a id="13103" class="Symbol">(</a><a id="13104" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13108" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13108" class="Bound">m</a><a id="13109" class="Symbol">)</a> <a id="13111" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="13137" class="Symbol">=</a>  <a id="13140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="13148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="13152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13004" class="Function">≤-total</a> <a id="13160" class="Symbol">(</a><a id="13161" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13165" class="Bound">m</a><a id="13166" class="Symbol">)</a> <a id="13168" class="Symbol">(</a><a id="13169" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13173" class="Bound">n</a><a id="13174" class="Symbol">)</a> <a id="13176" class="Keyword">with</a> <a id="13181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13004" class="Function">≤-total</a> <a id="13189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13165" class="Bound">m</a> <a id="13191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13173" class="Bound">n</a>
<a id="13193" class="Symbol">...</a>                        <a id="13220" class="Symbol">|</a> <a id="13222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="13230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13230" class="Bound">m≤n</a>  <a id="13235" class="Symbol">=</a>  <a id="13238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="13246" class="Symbol">(</a><a id="13247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="13251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13230" class="Bound">m≤n</a><a id="13254" class="Symbol">)</a>
<a id="13256" class="Symbol">...</a>                        <a id="13283" class="Symbol">|</a> <a id="13285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="13293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13293" class="Bound">n≤m</a>  <a id="13298" class="Symbol">=</a>  <a id="13301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="13309" class="Symbol">(</a><a id="13310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="13314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13293" class="Bound">n≤m</a><a id="13317" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="14825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14825" class="Function">≤-total′</a> <a id="14834" class="Symbol">:</a> <a id="14836" class="Symbol">∀</a> <a id="14838" class="Symbol">(</a><a id="14839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14839" class="Bound">m</a> <a id="14841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14841" class="Bound">n</a> <a id="14843" class="Symbol">:</a> <a id="14845" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14846" class="Symbol">)</a> <a id="14848" class="Symbol">→</a> <a id="14850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="14856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14839" class="Bound">m</a> <a id="14858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14841" class="Bound">n</a>
<a id="14860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14825" class="Function">≤-total′</a> <a id="14869" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14877" class="Bound">n</a>        <a id="14886" class="Symbol">=</a>  <a id="14889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="14897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="14901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14825" class="Function">≤-total′</a> <a id="14910" class="Symbol">(</a><a id="14911" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14915" class="Bound">m</a><a id="14916" class="Symbol">)</a> <a id="14918" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="14927" class="Symbol">=</a>  <a id="14930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="14938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="14942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14825" class="Function">≤-total′</a> <a id="14951" class="Symbol">(</a><a id="14952" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14956" class="Bound">m</a><a id="14957" class="Symbol">)</a> <a id="14959" class="Symbol">(</a><a id="14960" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14964" class="Bound">n</a><a id="14965" class="Symbol">)</a>  <a id="14968" class="Symbol">=</a>  <a id="14971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15003" class="Function">helper</a> <a id="14978" class="Symbol">(</a><a id="14979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14825" class="Function">≤-total′</a> <a id="14988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14956" class="Bound">m</a> <a id="14990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14964" class="Bound">n</a><a id="14991" class="Symbol">)</a>
  <a id="14995" class="Keyword">where</a>
  <a id="15003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15003" class="Function">helper</a> <a id="15010" class="Symbol">:</a> <a id="15012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="15018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14956" class="Bound">m</a> <a id="15020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14964" class="Bound">n</a> <a id="15022" class="Symbol">→</a> <a id="15024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="15030" class="Symbol">(</a><a id="15031" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14956" class="Bound">m</a><a id="15036" class="Symbol">)</a> <a id="15038" class="Symbol">(</a><a id="15039" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14964" class="Bound">n</a><a id="15044" class="Symbol">)</a>
  <a id="15048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15003" class="Function">helper</a> <a id="15055" class="Symbol">(</a><a id="15056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="15064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15064" class="Bound">m≤n</a><a id="15067" class="Symbol">)</a>  <a id="15070" class="Symbol">=</a>  <a id="15073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="15081" class="Symbol">(</a><a id="15082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15064" class="Bound">m≤n</a><a id="15089" class="Symbol">)</a>
  <a id="15093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15003" class="Function">helper</a> <a id="15100" class="Symbol">(</a><a id="15101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="15109" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15109" class="Bound">n≤m</a><a id="15112" class="Symbol">)</a>  <a id="15115" class="Symbol">=</a>  <a id="15118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="15126" class="Symbol">(</a><a id="15127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15109" class="Bound">n≤m</a><a id="15134" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="15772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15772" class="Function">≤-total″</a> <a id="15781" class="Symbol">:</a> <a id="15783" class="Symbol">∀</a> <a id="15785" class="Symbol">(</a><a id="15786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15786" class="Bound">m</a> <a id="15788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15788" class="Bound">n</a> <a id="15790" class="Symbol">:</a> <a id="15792" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15793" class="Symbol">)</a> <a id="15795" class="Symbol">→</a> <a id="15797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11665" class="Datatype">Total</a> <a id="15803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15786" class="Bound">m</a> <a id="15805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15788" class="Bound">n</a>
<a id="15807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15772" class="Function">≤-total″</a> <a id="15816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15816" class="Bound">m</a>       <a id="15824" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="15850" class="Symbol">=</a>  <a id="15853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="15861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="15865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15772" class="Function">≤-total″</a> <a id="15874" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15882" class="Symbol">(</a><a id="15883" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15887" class="Bound">n</a><a id="15888" class="Symbol">)</a>                   <a id="15908" class="Symbol">=</a>  <a id="15911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="15919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="15923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15772" class="Function">≤-total″</a> <a id="15932" class="Symbol">(</a><a id="15933" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15937" class="Bound">m</a><a id="15938" class="Symbol">)</a> <a id="15940" class="Symbol">(</a><a id="15941" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15945" class="Bound">n</a><a id="15946" class="Symbol">)</a> <a id="15948" class="Keyword">with</a> <a id="15953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15772" class="Function">≤-total″</a> <a id="15962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15937" class="Bound">m</a> <a id="15964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15945" class="Bound">n</a>
<a id="15966" class="Symbol">...</a>                        <a id="15993" class="Symbol">|</a> <a id="15995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="16003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16003" class="Bound">m≤n</a>   <a id="16009" class="Symbol">=</a>  <a id="16012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="InductiveConstructor">forward</a> <a id="16020" class="Symbol">(</a><a id="16021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="16025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16003" class="Bound">m≤n</a><a id="16028" class="Symbol">)</a>
<a id="16030" class="Symbol">...</a>                        <a id="16057" class="Symbol">|</a> <a id="16059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="16067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16067" class="Bound">n≤m</a>   <a id="16073" class="Symbol">=</a>  <a id="16076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11753" class="InductiveConstructor">flipped</a> <a id="16084" class="Symbol">(</a><a id="16085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="16089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16067" class="Bound">n≤m</a><a id="16092" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="16697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Function">+-monoʳ-≤</a> <a id="16707" class="Symbol">:</a> <a id="16709" class="Symbol">∀</a> <a id="16711" class="Symbol">(</a><a id="16712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16712" class="Bound">n</a> <a id="16714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16714" class="Bound">p</a> <a id="16716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16716" class="Bound">q</a> <a id="16718" class="Symbol">:</a> <a id="16720" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16721" class="Symbol">)</a>
  <a id="16725" class="Symbol">→</a> <a id="16727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16714" class="Bound">p</a> <a id="16729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16716" class="Bound">q</a>
    <a id="16737" class="Comment">-------------</a>
  <a id="16753" class="Symbol">→</a> <a id="16755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16712" class="Bound">n</a> <a id="16757" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16714" class="Bound">p</a> <a id="16761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="16763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16712" class="Bound">n</a> <a id="16765" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16716" class="Bound">q</a>
<a id="16769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Function">+-monoʳ-≤</a> <a id="16779" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="16787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16787" class="Bound">p</a> <a id="16789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16789" class="Bound">q</a> <a id="16791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16791" class="Bound">p≤q</a>  <a id="16796" class="Symbol">=</a>  <a id="16799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16791" class="Bound">p≤q</a>
<a id="16803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Function">+-monoʳ-≤</a> <a id="16813" class="Symbol">(</a><a id="16814" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16818" class="Bound">n</a><a id="16819" class="Symbol">)</a> <a id="16821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16821" class="Bound">p</a> <a id="16823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16823" class="Bound">q</a> <a id="16825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16825" class="Bound">p≤q</a>  <a id="16830" class="Symbol">=</a>  <a id="16833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="16837" class="Symbol">(</a><a id="16838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Function">+-monoʳ-≤</a> <a id="16848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16818" class="Bound">n</a> <a id="16850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16821" class="Bound">p</a> <a id="16852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16823" class="Bound">q</a> <a id="16854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16825" class="Bound">p≤q</a><a id="16857" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="17513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17513" class="Function">+-monoˡ-≤</a> <a id="17523" class="Symbol">:</a> <a id="17525" class="Symbol">∀</a> <a id="17527" class="Symbol">(</a><a id="17528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17528" class="Bound">m</a> <a id="17530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17530" class="Bound">n</a> <a id="17532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17532" class="Bound">p</a> <a id="17534" class="Symbol">:</a> <a id="17536" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17537" class="Symbol">)</a>
  <a id="17541" class="Symbol">→</a> <a id="17543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17528" class="Bound">m</a> <a id="17545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17530" class="Bound">n</a>
    <a id="17553" class="Comment">-------------</a>
  <a id="17569" class="Symbol">→</a> <a id="17571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17528" class="Bound">m</a> <a id="17573" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17532" class="Bound">p</a> <a id="17577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17530" class="Bound">n</a> <a id="17581" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17532" class="Bound">p</a>
<a id="17585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17513" class="Function">+-monoˡ-≤</a> <a id="17595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17595" class="Bound">m</a> <a id="17597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17597" class="Bound">n</a> <a id="17599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">p</a> <a id="17601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17601" class="Bound">m≤n</a>  <a id="17606" class="Keyword">rewrite</a> <a id="17614" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="17621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17595" class="Bound">m</a> <a id="17623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">p</a> <a id="17625" class="Symbol">|</a> <a id="17627" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="17634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17597" class="Bound">n</a> <a id="17636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">p</a>  <a id="17639" class="Symbol">=</a> <a id="17641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Function">+-monoʳ-≤</a> <a id="17651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">p</a> <a id="17653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17595" class="Bound">m</a> <a id="17655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17597" class="Bound">n</a> <a id="17657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17601" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="17871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17871" class="Function">+-mono-≤</a> <a id="17880" class="Symbol">:</a> <a id="17882" class="Symbol">∀</a> <a id="17884" class="Symbol">(</a><a id="17885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17885" class="Bound">m</a> <a id="17887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17887" class="Bound">n</a> <a id="17889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="Bound">p</a> <a id="17891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17891" class="Bound">q</a> <a id="17893" class="Symbol">:</a> <a id="17895" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17896" class="Symbol">)</a>
  <a id="17900" class="Symbol">→</a> <a id="17902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17885" class="Bound">m</a> <a id="17904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17887" class="Bound">n</a>
  <a id="17910" class="Symbol">→</a> <a id="17912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="Bound">p</a> <a id="17914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17891" class="Bound">q</a>
    <a id="17922" class="Comment">-------------</a>
  <a id="17938" class="Symbol">→</a> <a id="17940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17885" class="Bound">m</a> <a id="17942" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="Bound">p</a> <a id="17946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17887" class="Bound">n</a> <a id="17950" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17891" class="Bound">q</a>
<a id="17954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17871" class="Function">+-mono-≤</a> <a id="17963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17963" class="Bound">m</a> <a id="17965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17965" class="Bound">n</a> <a id="17967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17967" class="Bound">p</a> <a id="17969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17969" class="Bound">q</a> <a id="17971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17971" class="Bound">m≤n</a> <a id="17975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17975" class="Bound">p≤q</a>  <a id="17980" class="Symbol">=</a>  <a id="17983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="17991" class="Symbol">(</a><a id="17992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17513" class="Function">+-monoˡ-≤</a> <a id="18002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17963" class="Bound">m</a> <a id="18004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17965" class="Bound">n</a> <a id="18006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17967" class="Bound">p</a> <a id="18008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17971" class="Bound">m≤n</a><a id="18011" class="Symbol">)</a> <a id="18013" class="Symbol">(</a><a id="18014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16697" class="Function">+-monoʳ-≤</a> <a id="18024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17965" class="Bound">n</a> <a id="18026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17967" class="Bound">p</a> <a id="18028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17969" class="Bound">q</a> <a id="18030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17975" class="Bound">p≤q</a><a id="18033" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

<pre class="Agda">{% raw %}<a id="18358" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
<pre class="Agda">{% raw %}<a id="18507" class="Keyword">infix</a> <a id="18513" class="Number">4</a> <a id="18515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18525" class="Datatype Operator">_&lt;_</a>

<a id="18520" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18525" class="Datatype Operator">_&lt;_</a> <a id="18529" class="Symbol">:</a> <a id="18531" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18533" class="Symbol">→</a> <a id="18535" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18537" class="Symbol">→</a> <a id="18539" class="PrimitiveType">Set</a> <a id="18543" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18552" class="InductiveConstructor">z&lt;s</a> <a id="18556" class="Symbol">:</a> <a id="18558" class="Symbol">∀</a> <a id="18560" class="Symbol">{</a><a id="18561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18561" class="Bound">n</a> <a id="18563" class="Symbol">:</a> <a id="18565" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18566" class="Symbol">}</a>
      <a id="18574" class="Comment">------------</a>
    <a id="18591" class="Symbol">→</a> <a id="18593" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18525" class="Datatype Operator">&lt;</a> <a id="18600" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18561" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18609" class="InductiveConstructor">s&lt;s</a> <a id="18613" class="Symbol">:</a> <a id="18615" class="Symbol">∀</a> <a id="18617" class="Symbol">{</a><a id="18618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18618" class="Bound">m</a> <a id="18620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18620" class="Bound">n</a> <a id="18622" class="Symbol">:</a> <a id="18624" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18625" class="Symbol">}</a>
    <a id="18631" class="Symbol">→</a> <a id="18633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18618" class="Bound">m</a> <a id="18635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18525" class="Datatype Operator">&lt;</a> <a id="18637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18620" class="Bound">n</a>
      <a id="18645" class="Comment">-------------</a>
    <a id="18663" class="Symbol">→</a> <a id="18665" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18618" class="Bound">m</a> <a id="18671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18525" class="Datatype Operator">&lt;</a> <a id="18673" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18620" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

<pre class="Agda">{% raw %}<a id="19847" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).)

<pre class="Agda">{% raw %}<a id="20336" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

<pre class="Agda">{% raw %}<a id="20561" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

<pre class="Agda">{% raw %}<a id="20720" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

<pre class="Agda">{% raw %}<a id="20996" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
<pre class="Agda">{% raw %}<a id="21251" class="Keyword">data</a> <a id="even"></a><a id="21256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="21261" class="Symbol">:</a> <a id="21263" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="21265" class="Symbol">→</a> <a id="21267" class="PrimitiveType">Set</a>
<a id="21271" class="Keyword">data</a> <a id="odd"></a><a id="21276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21276" class="Datatype">odd</a>  <a id="21281" class="Symbol">:</a> <a id="21283" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="21285" class="Symbol">→</a> <a id="21287" class="PrimitiveType">Set</a>

<a id="21292" class="Keyword">data</a> <a id="21297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="21302" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21311" class="InductiveConstructor">zero</a> <a id="21316" class="Symbol">:</a>
      <a id="21324" class="Comment">---------</a>
      <a id="21340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="21345" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21353" class="InductiveConstructor">suc</a>  <a id="21358" class="Symbol">:</a> <a id="21360" class="Symbol">∀</a> <a id="21362" class="Symbol">{</a><a id="21363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21363" class="Bound">n</a> <a id="21365" class="Symbol">:</a> <a id="21367" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21368" class="Symbol">}</a>
    <a id="21374" class="Symbol">→</a> <a id="21376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21276" class="Datatype">odd</a> <a id="21380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21363" class="Bound">n</a>
      <a id="21388" class="Comment">------------</a>
    <a id="21405" class="Symbol">→</a> <a id="21407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="21412" class="Symbol">(</a><a id="21413" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21363" class="Bound">n</a><a id="21418" class="Symbol">)</a>

<a id="21421" class="Keyword">data</a> <a id="21426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21276" class="Datatype">odd</a> <a id="21430" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21439" class="InductiveConstructor">suc</a>   <a id="21445" class="Symbol">:</a> <a id="21447" class="Symbol">∀</a> <a id="21449" class="Symbol">{</a><a id="21450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21450" class="Bound">n</a> <a id="21452" class="Symbol">:</a> <a id="21454" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21455" class="Symbol">}</a>
    <a id="21461" class="Symbol">→</a> <a id="21463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="21468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21450" class="Bound">n</a>
      <a id="21476" class="Comment">-----------</a>
    <a id="21492" class="Symbol">→</a> <a id="21494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21276" class="Datatype">odd</a> <a id="21498" class="Symbol">(</a><a id="21499" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21450" class="Bound">n</a><a id="21504" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="22680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22680" class="Function">e+e≡e</a> <a id="22686" class="Symbol">:</a> <a id="22688" class="Symbol">∀</a> <a id="22690" class="Symbol">{</a><a id="22691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22691" class="Bound">m</a> <a id="22693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22693" class="Bound">n</a> <a id="22695" class="Symbol">:</a> <a id="22697" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22698" class="Symbol">}</a>
  <a id="22702" class="Symbol">→</a> <a id="22704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="22709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22691" class="Bound">m</a>
  <a id="22713" class="Symbol">→</a> <a id="22715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="22720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22693" class="Bound">n</a>
    <a id="22726" class="Comment">------------</a>
  <a id="22741" class="Symbol">→</a> <a id="22743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="22748" class="Symbol">(</a><a id="22749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22691" class="Bound">m</a> <a id="22751" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22693" class="Bound">n</a><a id="22754" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22757" class="Function">o+e≡o</a> <a id="22763" class="Symbol">:</a> <a id="22765" class="Symbol">∀</a> <a id="22767" class="Symbol">{</a><a id="22768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22768" class="Bound">m</a> <a id="22770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22770" class="Bound">n</a> <a id="22772" class="Symbol">:</a> <a id="22774" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22775" class="Symbol">}</a>
  <a id="22779" class="Symbol">→</a> <a id="22781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21276" class="Datatype">odd</a> <a id="22785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22768" class="Bound">m</a>
  <a id="22789" class="Symbol">→</a> <a id="22791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21256" class="Datatype">even</a> <a id="22796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22770" class="Bound">n</a>
    <a id="22802" class="Comment">-----------</a>
  <a id="22816" class="Symbol">→</a> <a id="22818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21276" class="Datatype">odd</a> <a id="22822" class="Symbol">(</a><a id="22823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22768" class="Bound">m</a> <a id="22825" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22770" class="Bound">n</a><a id="22828" class="Symbol">)</a>

<a id="22831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22680" class="Function">e+e≡e</a> <a id="22837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21311" class="InductiveConstructor">zero</a>     <a id="22846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22846" class="Bound">en</a>  <a id="22850" class="Symbol">=</a>  <a id="22853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22846" class="Bound">en</a>
<a id="22856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22680" class="Function">e+e≡e</a> <a id="22862" class="Symbol">(</a><a id="22863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21353" class="InductiveConstructor">suc</a> <a id="22867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22867" class="Bound">om</a><a id="22869" class="Symbol">)</a> <a id="22871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22871" class="Bound">en</a>  <a id="22875" class="Symbol">=</a>  <a id="22878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21353" class="InductiveConstructor">suc</a> <a id="22882" class="Symbol">(</a><a id="22883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22757" class="Function">o+e≡o</a> <a id="22889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22867" class="Bound">om</a> <a id="22892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22871" class="Bound">en</a><a id="22894" class="Symbol">)</a>

<a id="22897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22757" class="Function">o+e≡o</a> <a id="22903" class="Symbol">(</a><a id="22904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21439" class="InductiveConstructor">suc</a> <a id="22908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22908" class="Bound">em</a><a id="22910" class="Symbol">)</a> <a id="22912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22912" class="Bound">en</a>  <a id="22916" class="Symbol">=</a>  <a id="22919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21439" class="InductiveConstructor">suc</a> <a id="22923" class="Symbol">(</a><a id="22924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22680" class="Function">e+e≡e</a> <a id="22930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22908" class="Bound">em</a> <a id="22933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22912" class="Bound">en</a><a id="22935" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

<pre class="Agda">{% raw %}<a id="24089" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

<pre class="Agda">{% raw %}<a id="25382" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda">{% raw %}<a id="25534" class="Keyword">import</a> <a id="25541" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="25550" class="Keyword">using</a> <a id="25556" class="Symbol">(</a><a id="25557" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="25560" class="Symbol">;</a> <a id="25562" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="25565" class="Symbol">;</a> <a id="25567" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="25570" class="Symbol">)</a>
<a id="25572" class="Keyword">import</a> <a id="25579" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25599" class="Keyword">using</a> <a id="25605" class="Symbol">(</a><a id="25606" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2115" class="Function">≤-refl</a><a id="25612" class="Symbol">;</a> <a id="25614" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2308" class="Function">≤-trans</a><a id="25621" class="Symbol">;</a> <a id="25623" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2165" class="Function">≤-antisym</a><a id="25632" class="Symbol">;</a> <a id="25634" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2420" class="Function">≤-total</a><a id="25641" class="Symbol">;</a>
                                  <a id="25677" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12667" class="Function">+-monoʳ-≤</a><a id="25686" class="Symbol">;</a> <a id="25688" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12577" class="Function">+-monoˡ-≤</a><a id="25697" class="Symbol">;</a> <a id="25699" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12421" class="Function">+-mono-≤</a><a id="25707" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
