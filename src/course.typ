#import "@preview/polylux:0.4.0": *
#import "@preview/metropolis-polylux:0.1.0" as metropolis
#import "@preview/curryst:0.6.0": *
#import "@preview/cades:0.3.1": qr-code
#import metropolis: new-section, focus

#let rule-set(column-gutter: 3em, row-gutter: 2em, ..rules) = {
  set par(leading: row-gutter)
  block(rules.pos().map(box).join(h(column-gutter, weak: true)))
}

#show: metropolis.setup


#slide[
  #set page(header: none, footer: none, margin: 3em)

 
  #text(size: 1.3em)[
    *Introduction to Information Flow Control*
  ]

  #metropolis.divider
  
  #set text(size: .8em, weight: "light")
  Alix Peigue

  May 2026
]

#slide[
  = Agenda

  #metropolis.outline
]

#new-section[What Is Information Flow Control ?]

#slide[
  = Context

  Some programs have access to sensitive variables, e.g.
  - passwords
  - cryprographic keys

  We want to make sure that the programs cannot leak these informations
]

#slide[
  = Program model

  The program
  - takes private inputs and public inputs
  - produces private outputs and public outputs
]

#slide[
  = Attacker model

  - Knows the code of the program
  - Can control public inputs and see public outputs of the program
]

#slide[
  = Goal

  Prevent the attacker from _deducing private inputs from the public outputs_
   - _Noninterference_: private inputs do not influence public outputs
]

#slide[
  = Implicit and explicit flow

  $h$ is a private boolean variable, $l$ is a public boolean variable

  Explicit flow
  ```js
  l = h // private variable is explicitely leaked to the public
  ```

  Implicit flow
  ```js
  if(h) {
    l = true;
  } else {
    l = false
  } // private variable is implicitely leaked
  ```

  _Goal_: detect all implicit and explicit flows from private variables to public variables
]

#slide[
  = How ?

  - _Static control_: analyze the program before it runs and prevent execution if it is unsecure
  - _Dynamic control_: monitor the program while it runs and stop if it leaks private data
]

#new-section[Static Control]

#slide[
  = Definitions

  _Security lattice_: $(cal(L), subset.sq.eq, union.sq, inter.sq, top, bot)$
  - $cal(L) = {H, L}$ the set of security labels
  - $subset.eq.sq$ the ordering relation : $L subset.sq.eq H, H subset.sq.eq.not L$
    - Information can flow from $L$ to $H$ but not from $H$ to $L$
  - $union.sq$ the join operator, $L union.sq H = H$
  - $inter.sq$ the meet operator, $L inter.sq H = L$
  - $top = H$, the highest label
  - $bot = L$, the lowest label
  
]

#slide[
  = Definitions

  - A program has a security environment $Gamma : "Vars" -> cal(L)$ : each variable in the program has a security label
  - We track a program context $p c in cal(L)$ during the checking of the program
  - $tack e: l$ means that the expression $e$ has label $l$. Similarly, $p c tack P$ means that the program $P$ is typable in the security context $p c$.
  - Inference rules define whether a program is valid and are of the form #prooftree(rule("premise 1", "premise 2", "...", "conclusion")) meaning if all premises are true the the conclusion is true
  - All the inference rules define a _security type system_

  
]


#slide[
  = Inference rules

  Basic language grammar

  ```
  e ::= true | false | n (literal) | x (variable name)
  P ::= skip | x=e | P1;P2 | if e then P1 else P2 | while e do P
  ```

  With the following inference rules

  #text(18pt)[
  
  #align(center, rule-set(
    prooftree(
      rule(
        name: smallcaps("High-Exp"),
        $$,
        $tack e:H$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Low-Exp"),
        $forall x in "Vars"(e).Gamma(x) = L$,
        $tack e:L$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Low-Assign"),
        $Gamma(x) = L$,
        $tack e:L$,
        $L tack x=e$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("High-Assign"),
        $Gamma(x) = H$,
        $p c tack x = e$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Skip"),
        $$,
        $p c tack "skip"$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Seq"),
        $p c tack P_1$,
        $p c tack P_2$,
        $p c tack P_1;P_2$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("If"),
        $tack e: p c$,
        $ p c tack P_1$,
        $ p c tack P_2$,
        $p c tack "if" e "then" P_1 "else" P_2$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("While"),
        $tack e: p c$,
        $p c tack P$,
        $p c tack "if" e "do" P$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Sub"),
        $H tack P$,
        $L tack P$
      )
    )
    
  ))

  ]

]

#slide[
  = Examples
  #text(16pt)[#align(center, rule-set(
    prooftree(
      rule(
        name: smallcaps("Low-Exp"),
        $forall x in "Vars"(e).Gamma(x) = L$,
        $tack e:L$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Low-Assign"),
        $Gamma(x) = L$,
        $tack e:L$,
        $L tack x=e$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("High-Assign"),
        $Gamma(x) = H$,
        $p c tack x = e$
      )
    ),
  ))]
  
  Let's say that $Gamma(l) = L, Gamma(h) = H$

  ```js
  l = h; // How can we know that this flow is illegal ?
  ```

  #uncover(2)[
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps("Low-Assign"),
          text(green)[$Gamma(l) = L$],
          rule(
            name: smallcaps("Low-Exp"),
            text(red)[$forall x in "Vars"(h).Gamma(x) = L$],
            $tack h:L$
          ),
          $L tack l=h$
        )
      ),
      prooftree(
        rule(
          name: smallcaps("High-Assign"),
          text(red)[$Gamma(l) = H$],
          $L tack l = h$
        )
      ),
    ))
  ]
]

#slide[
  = Examples


  #text(12pt)[
  
  #align(center, rule-set(
    prooftree(
      rule(
        name: smallcaps("High-Exp"),
        $$,
        $tack e:H$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Low-Exp"),
        $forall x in "Vars"(e).Gamma(x) = L$,
        $tack e:L$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Low-Assign"),
        $Gamma(x) = L$,
        $tack e:L$,
        $L tack x=e$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("High-Assign"),
        $Gamma(x) = H$,
        $p c tack x = e$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("If"),
        $tack e: p c$,
        $ p c tack P_1$,
        $ p c tack P_2$,
        $p c tack "if" e "then" P_1 "else" P_2$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Sub"),
        $H tack P$,
        $L tack P$
      )
    )
    
  ))

  ]
  Let's say that $Gamma(l) = L, Gamma(h) = H$

  ```haskell
  if h then l = true else l = false
  ```

  #set text(15pt)
  
  #uncover(2)[
  
  #align(center, rule-set(
    prooftree(
      rule(
        name: smallcaps("If"),
        rule(
          name: smallcaps("Low-Exp"),
          text(red)[$forall x in "Vars"(e).Gamma(x) = L$],
          $tack e:L$
        ),
        prooftree(
          rule(
            text(green)[$Gamma(l) = L$],
            rule(
              text(green)[$forall x in "Vars"("true").Gamma(x) = L$],
              $tack "true":L$
            ),
            $L tack l="true"$
          )
        ),
        prooftree(
          rule(
            text(green)[$Gamma(l) = L$],
            rule(
              text(green)[$forall x in "Vars"("false").Gamma(x) = L$],
              $tack "false":L$
            ),
            $L tack l="false"$
          )
        ),
        $L tack "if" h "then" l="true" "else" l="false"$
      )
    ),
    prooftree(
      rule(
        name: smallcaps("Sub"),
        prooftree(
          rule(
            name: smallcaps("If"),
            rule(
              name: smallcaps("High-Exp"),
              text(green)[$tack e:H$]
            ),
            prooftree(
              rule(
                name: smallcaps("High-Assign"),
                text(red)[$Gamma(l) = H$],
                $H tack l = "false"$
              )
            ),
            prooftree(
              rule(
                name: smallcaps("High-Assign"),
                text(red)[$Gamma(l) = H$],
                $H tack l = "false"$
              )
            ),
            $H tack "if" h "then" l="true" "else" l="false"$
          )
        ),
        $L tack "if" h "then" l="true" "else" l="false"$
      )
    )
  ))

  ]
]

#slide[
  = Pros & Cons of Static Information Flow Control

  Pros
  - No runtime overhead

  Cons
  - Can be too restrictive (some programs that do not leak data can be rejected by the type system)
]

#new-section[Dynamic Control]

#slide[
  = Overall principles

  - Create a monitor that tracks the security label of values
  - Apply monitor rules
  - Kill the program if a monitor rule is broken
]

#slide[
  = Definitions

  - The program has a memory $m$, $m' = m[x -> a]$ means $m'$ is $m$ but with the value $a$ assigned to the valiable $x$
  - The security context $cal(C) = (p c, e c, r c)$ is composed of the program context, the exception context and the return context.
    It tracks the various security levels during the execution of the program
  - In the program, variables contain labeled values, written $n^l$. $n$ is the value and $l$ is the label, e.g. $5^"high"$ is the number 5 with label high
  - $cal(C) tack chevron.l P, m chevron.r --> m'$ means that the evaluation of statement $P$ on memory $m$ produces memory $m'$ and is safe in program context $cal(C)$
  - $cal(C) tack chevron.l e, m chevron.r --> chevron.l n^l, m' chevron.r$ means that the evaluation of expression $e$ in memory $m$ evaluate to the value labeled $n^l$, produces memory $m'$ and is safe in context $cal(C)$
]

#slide[
  = Understanting monitor rules

  
  #text(14pt)[
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps("M-Assign"),
          $(p c, e c, r c) tack chevron.l e, m chevron.r --> chevron.l n^l, m' chevron.r$,
          $m'(x) = n_0^l_0$,
          $p c subset.sq.eq l_0$,
          $(p c, e c, r c) tack chevron.l x=e, m chevron.r --> m'[x-->n^(l union.sq p c)]$
        )
      ),
      prooftree(
        rule(
          name: smallcaps("M-Literal"),
          $cal(C) tack chevron.l n, m chevron.r --> chevron.l n^"low", m chevron.r$
        )
      )
    ))
  ]


  #text(22pt)[Let's try to evaluate the program $x = 2$ in memory $m = {x -> 1^"low"}$ and context $cal(C) = ("high", e c, r c)$] 

  
  #text(16pt)[
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps("M-Assign"),
          rule(
            name: smallcaps("M-Literal"),
            text(green)[$("high", e c, r c) tack chevron.l 2, {} chevron.r --> chevron.l 2^"high", {} chevron.r$],
          ),
          text(green)[$m(x) = 1^"low"$],
          text(red)[$"high" subset.sq.eq "low"$],
          $("high", e c, r c) tack chevron.l x = 2, m chevron.r --> m'[x-->2^"high"]$
        )
      )
    ))
  ]

  
  #text(22pt)[The evaluation of the statement is invalid with these monitor rules, so the program is stopped] 
]

#slide[
  = Pros & Cons of Dynamic Information Flow Control

  Pros
  - More fine-grained that static IFC
  - Necessary for highly dynamic languages like JavaScript or Python

  Cons
  - Runtime overhead, needs an interpreter for the language
]

#new-section[Interactive examples]

#slide[
  = Let's try some examples

  Go to _ https://dynamicflowchallenge.github.io _

  #align(center,
    qr-code("https://dynamicflowchallenge.github.io/")
  )
]

#slide[
  = Challenge One

  For challenge one, there is only one monitor rule

  #prooftree(
    rule(
      name: smallcaps("M-Assign"),
      $(p c, e c, r c) tack chevron.l e, m chevron.r --> chevron.l n^l, m' chevron.r$,
      $(p c, e c, r c) tack chevron.l x = e, m chevron.r --> m'[x -> n^(p c)]$,
    )
  )

  The program starts with $h$ containing a boolean value with label high. The goal is to have $l$ contain the same value as $h$, but with label low

  #uncover(2)[
  Solution: 
  ```js
  l = h
  ```
  ]

]


#slide[
  = Challenge Two

  #smallcaps("M-Assign") has been modified to correct the error in challenge one, it is now
  #prooftree(
    rule(
      name: smallcaps("M-Assign"),
      $(p c, e c, r c) tack chevron.l e, m chevron.r --> chevron.l n^l, m' chevron.r$,
      $(p c, e c, r c) tack chevron.l x = e, m chevron.r --> m'[x -> n^(l union.sq p c)]$,
    )
  )
  
  #uncover(2)[
  Solution: 
  ```js
  l = false;
  if (h) {
    l = true;
  }
  ```
  ]
]

#slide[
  = Challenge Three

  Oops, seems like he had forgotten about implicit flow, we add the following monitor rules (and similar rules for `while`) to hopefully prevent it !

  #text(16pt)[
  #align(center, rule-set(
    prooftree(
      rule(
        name: smallcaps("M-IfFalse"),
        $(p c, e c, r c) tack chevron.l e, m chevron.r --> chevron.l "false"^l, m' chevron.r$,
        $(l union.sq p c, e c, r c) tack chevron.l c_2, m' chevron.r --> m''$,
        $(p c, e c, r c) tack chevron.l "if"(e) {c_1} "else" {c_2}, m chevron.r --> m''$,
      )
    ),
    prooftree(
      rule(
        name: smallcaps("M-IfTrue"),
        $(p c, e c, r c) tack chevron.l e, m chevron.r --> chevron.l "true"^l, m' chevron.r$,
        $(l union.sq p c, e c, r c) tack chevron.l c_1, m' chevron.r --> m''$,
        $(p c, e c, r c) tack chevron.l "if"(e) {c_1} "else" {c_2}, m chevron.r --> m''$,
      )
    )
  ))
  ]
    
  #uncover(2)[
  Solution: 
  ```js
  t = false; l = true;
  if (h) { t = true; }
  if (not t) { l = false; }
  ```
  ]
]

#slide[
  = Challenge Three: Explanation
   
  ```js
  t = false; l = true;
  if (h) { t = true; }
  if (not t) { l = false; }
  ```

  Let's think of the two cases :
  #columns(2)[
    - $h = "true"^"high"$: we enter the first if with pc high
    - $t = "true"^"high"$: we do not enter the second if
    - $l = "true"^"low"$ 
    #colbreak()
    - $h = "false"^"high"$: we do not enter the first if
    - $t = "false"^"low"$: we do enter the second if with pc low
    - $l = "false"^"low"$
  ]
]

#slide[
  = Challenge Three: Fixing the Error

  To fix the error from challenge three, we enforce the "No sensitive upgrade" rule that says that we cannot raise the label of a variable when assigning in secure context.
  #align(center, rule-set(
    prooftree(
      rule(
        name: smallcaps("M-Assign"),
        $(p c, e c, r c) tack chevron.l e, m chevron.r --> chevron.l n^l, m' chevron.r$,
        $m'(x) = n_0^l_0$,
        $p c subset.sq.eq l_0$,
        $(p c, e c, r c) tack chevron.l x=e, m chevron.r --> m'[x-->n^(l union.sq p c)]$
      )
    ),
  ))
]

#slide[
  = Next Challenges

  You are on your own for the last three challenges, they follow the same underlying logic as the first challenges.

  #align(center, text(50pt)[_ Good Luck !_])
]

#new-section[Related Work]

#slide[
  - JSFlow @jsflow, a security-enhanced JavaScript interpreter for information flow (_ https://www.jsflow.net/ _)
  - Troupe @troupe, a  programming language for concurrent and distributed programming with dynamic information flow control (_ https://troupe.cs.au.dk/ _)
  - Jif @jif, a security-typed extention of Java (_ https://www.cs.cornell.edu/jif/ _)

  You can also check the Information Flow Control Challenge for more challenging exercises with a security type system (_ https://ifc-challenge.appspot.com/ _).
]

#slide[
  #set text(20pt)
  #bibliography("references.bib", full: true)
]
