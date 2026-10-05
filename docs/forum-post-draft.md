# Draft: registration e-mail + reply to tetrationforum.org thread tid=1824

## 0. Registration is by e-mail only

`member.php?action=register` returns:

> Automated registrations are disabled due to increasing problems with
> automated users/bots. If you are a human, please send an e-mail to the forum
> staff tetrationforum(at)gmail.com asking for registration, including your
> preferred username, mathematical skill level/education and some sentences
> that make clear that you are a human with interest in this board.

So there is no form to fill in at all. Send this from your own mailbox (edit
the background paragraph — it should be true of you, and it is the part the
staff actually read):

    To:      tetrationforum@gmail.com
    Subject: Registration request

    Hello,

    I would like to request an account on the Tetration Forum.

    Preferred username: <pick one>

    Background: I am a software engineer working on numerics rather than a
    professional mathematician. Over the past months I have built a Python
    library that computes Kneser's tetration -- sexp, slog and continuous
    iteration of exp -- from a 50-digit Taylor table produced by a contraction
    in mpmath, extended to arbitrary real and complex bases, and I have been
    working through Kneser's 1950 paper and the Trappmann-Kouznetsov and
    Paulsen-Cowgill uniqueness results in detail.

    What I would like to post about first: I cross-checked that library against
    the reference values Lightrunner published in the thread "Mixed-base
    tetration: five preprints, a faster fatou.gp fork, and a base-change
    calculator". The two constructions agree to 52 digits for bases e and 2,
    which is an independent confirmation of the solution rather than just of
    the residual -- and one entry in that reference set (sexp base 2 at height
    1/2, the 1000-digit one) appears to be wrong from digit 44 on, which I
    would like to report in that thread.

    Thank you for maintaining the forum.

    <your name>

---

## 1. Reply to tid=1824 (post this once the account exists)

**Target:** https://tetrationforum.org/showthread.php?tid=1824
("Mixed-base tetration: five preprints, a faster fatou.gp fork, and a
base-change calculator", by Lightrunner / Janis)

**Why one reply and not two:** both items are answers to what Janis explicitly
asked for in that post — "feedback, especially about possible errors ... and
the claimed error bounds". Splitting them across two posts in the same thread
would read as padding. Item 1 is the independent confirmation, item 2 is the
defect.

**Not included** (say the word and I'll add it): the Shell–Thron finding — that
inside the region fatou.gp's merged solution and the regular Koenigs solution
are different functions. That is a fact about our library's default, not about
Janis's dataset, and sheldonison already documented it in tid=729.

---

### Post body (BBCode-ready; the forum uses MyBB)

Hi Janis,

thank you for publishing the reference values with their verification depths —
that is exactly the artefact the field was missing, and it let me do something
I could not do before. Two pieces of feedback, one good and one a defect
report.

[b]1. Independent confirmation of the base-e and base-2 values to 52 digits[/b]

I maintain a small Python library that computes Kneser's tetration by a
different route: a single Taylor table at 0, obtained by a contraction in
mpmath, with no PARI involved and no shared code with fatou.gp. Against your
80-digit grid it reproduces

[code]
sexp, base e    16 points, x = -0.4375 ... 1.4375    worst rel. dev. 1.1e-52
slog, base e    16 points, x = 1.25 ... 5.0          worst rel. dev. 1.5e-52
sexp, base 2    16 points                            worst rel. dev. 5.2e-53
slog, base 2    16 points                            worst rel. dev. 7.6e-53
sexp, base 10   16 points                            worst rel. dev. 1.5e-19
[/code]

(the base-10 row is a 17-digit table built on demand, so 1.5e-19 is its own
limit, not yours). And at the deep point,

[code]
sexp_e(1/2)  vs your 200/500/700/1000-digit entries   agrees to > 52 digits
sexp_2(1/2)  vs your 200-digit entry                  agrees to > 52 digits
[/code]

This matters more than it may look. Residual checks — |sexp(z+1) - b^sexp(z)|,
or |f(f(x)) - e^x| for the half-iterate — bound how well a table solves the
functional equation, but they do not bound the distance to Kneser's solution,
because the theta degree of freedom survives them. A second construction
agreeing to 52 digits does constrain that. So your values and fatou.gp now
independently corroborate each other's identification of the solution, not just
each other's arithmetic.

I also ran your vendored, unmodified fatou.gp myself for three bases outside
the Shell–Thron region, which your published set does not cover:

[code]
base      fatou.gp vs our two-fixed-point construction
3 + 2i    agrees to 2.0e-10
2 + 2i    agrees to 1.4e-10
-1 + i    agrees to 2.2e-10
[/code]

each at the residual floor of our 8-digit table. For -1 + i this also settled
which sheet our construction lands on — it is fatou.gp's (the conjugate sheet
is 1.5 away), which we had previously only inferred from conjugation symmetry.

Two practical notes from those runs, in case they are useful for the fork:
bases with imag(base) < 0 are much worse behaved — sexpinit(2+2*I) and
sexpinit(-1+1*I) each took about six minutes at \p 30, while sexpinit(3-2*I) at
the same precision had still not finished when I gave up on it much later.
(For scale, sexpinit(3+2*I) at \p 40 took ten minutes.) That matches Sheldon's
own remark in the tetcomplex.gp thread that the program "works best with
imag(base)>0".

[b]2. A defect: research/reference/values.json, entry sexp|2|0.5|1000[/b]

That entry disagrees with your own [i]sexp|2|0.5|200[/i] and
[i]sexp|2|0.5|500[/i] from digit 44 on:

[code]
ours (50 digits)   1.458781816036421700683971661038587135296606605330907102
your 200 and 500   1.458781816036421700683971661038587135296606605330907141
your 1000          1.458781816036421700683971661038587135296604326403002207
[/code]

Three things point at the 1000-digit entry being the outlier rather than the
other two: your 200- and 500-digit entries agree with each other over their
whole common length; your meta records the 200-digit one as verified to 194
digits via the error-vector pair; and our independent table agrees with both to
53 digits. The base-e 1000-digit entry is fine — it extends your 200/500/700
entries consistently, and our table agrees with it too.

I notice sexp|2|0.5|1000 is not among the entries listed under v2/v3/v4 in
meta, so I suspect it simply never got an error-vector partner and a bad run
was stored. The candidate_e_2000.txt header reports agreement against the
base-e references only, so it would not have caught this either.

Happy to send the comparison script if that is useful.

Thanks again for making all of this reproducible, and thanks to Sheldon for
fatou.gp, which is what made any of this checkable.
