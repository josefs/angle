
This is a proof-theoretic semantics, so rather than model the set of results that a query returns it describes how to prove that a query returns a given value.

Patterns:

$$ p ::= ()\ |\ num\ |\ ( p_{1} , p_{2})\ |\ inl\ p\ |\ inr\ p\ |\ [ p_{1} ,...,p_{n}]\ |\ \_\ |\ ( p_{1} | p_{2})\ |\ X\ |\ P\ p\ |\ q $$

Statement:

$$ s\ ::=\ p_{1} =p_{2} $$

Query:

$$ q\ ::=\ p\ \text{where} \ s_{1} ;\ ...;\ s_{n} $$

Query judgement

$$ \Gamma ;\ \Delta ;\ \Pi \ \vdash p\Longrightarrow v $$


$\displaystyle \Gamma$ is the environment, mapping variables to values
$\displaystyle \Delta$ is the database
$\displaystyle \Pi$ maps predicates to queries ($\displaystyle P\equiv q$), for derived predicates

Fact match

$$ \frac{\Gamma ;\ \Delta ,\ P\ v;\ \Pi \ \vdash \ p\Longrightarrow v}{\Gamma ;\ \Delta ,\ P\ v;\ \Pi \ \vdash P\ p\Longrightarrow P\ v} $$

Variable

$$ \frac{X\ \notin \ \Gamma}{\Gamma ,\ X=v;\ \Delta ;\ \Pi \ \vdash \ X\Longrightarrow v} $$

Datalog normally requires that X is restricted by something else in the query
otherwise we can choose arbitrary values for a variable, and nothing is checking that
the values are type-correct.


In Angle, different branches of $A | B$ can use the same variable name to mean different
variables provided the variable name isn't used outside. This semantics doesn't model that;
just rename the variables.

$$ \frac{\Gamma ; \Delta; \Pi \vdash p_1 \Longrightarrow v}{\Gamma ; \Delta; \Pi \vdash p_1 | \ p_2 \Longrightarrow v} $$
$$\frac{\Gamma ;\ \Delta ;\ \Pi \ \vdash \ p_{2} \Longrightarrow v}{\Gamma ;\ \Delta ;\ \Pi \ \vdash \ p_{1} \ |\ p_{2} \Longrightarrow v} $$
$$\frac{\Gamma ;\ \Delta ;\ \Pi \ \vdash \ p_{1} \Longrightarrow v \ \ \ \ \Gamma ;\ \Delta ;\ \Pi \ \vdash \ p_{2} \Longrightarrow v}{\Gamma ;\ \Delta ;\ \Pi \ \vdash \ p_{1} =p_{2}}$$

$$\frac{\Gamma ;\ \Delta ;\ \Pi \vdash p\Longrightarrow v\ \ \ \Gamma ;\ \Delta ;\ \Pi \vdash s_{1} \ ...\ \Gamma ;\ \Delta ;\ \Pi \vdash s_{n}}{\Gamma ;\ \Delta ;\ \Pi \vdash p\ \text{where} \ s_{1} ;\ ...;\ s_{n} \Longrightarrow v}$$

$$\frac{P\equiv q\in \Pi \ \ \ \ \ \ \ \Gamma ';\ \Delta ;\ \Pi \vdash q\Longrightarrow v\ \ \ \ \ \Gamma ;\ \Delta ;\ \Pi \vdash p\Longrightarrow v}{\Gamma ;\ \Delta ;\ \Pi \ \vdash P\ p\Longrightarrow P\ v} $$
