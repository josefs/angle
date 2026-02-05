The idea is that the semantics of a patterns is all the different values that it can take on. The main complication is variable assignment. Each result carries a set of variable assignments that was used to achieve the result. To make things compositional, each variable is initialized with the set of all values.

The tricky bit is that whenever we combine the result of two patterns, the variable assignments don't have to be equal; they just have to agree on the variables that they both assign. That's what the "compatible" relationship checks for.

We use $\Omega$ to mean the set of all values in Angle.


$$ [[ \cdot ]] :: \text{Pattern}, \text{Database} \rightarrow \{\text{Value},\text{Assignment)\}}$$
$$ [[\ v \ ]]_\Delta = \{ v_{\{\}} \} $$
$$ [[\ X\ ]]_\Delta = \{ v_{X := v} | v \in \Omega \} $$
$$ [[\ p_1\  |\ p_2\ ]]_\Delta = [[\ p_1\ ]]_\Delta \cup [[\ p_2\ ]]_\Delta $$
$$ [[\ (\ p_1,p_2\ )\ ]]_\Delta = \{ (v,w)_{\Gamma \cup \Pi} |\ v_\Gamma \in [[\ p_1\ ]]_\Delta, w_\Pi \in [[\ p_2\ ]]_\Delta, \text{compatible}(\Gamma,\Pi) \} $$
$$ [[\ P\ p\ ]]_\Delta = \{ v_\Gamma : v_\Gamma \in [[\ p\ ]]_\Delta, P\ v \in \Delta\ \} $$
$$ [[\ p\  \text{where}\ s_1 ; ... ; s_n ]]_\Delta = [[\ p\ ]]_\Delta \triangleleft\ \underset{i}{\dot{\bigcap}}[[\ s_i\ ]]_\Delta $$
$$ [[ \cdot ]] :: \text{Statment},\text{Database} \rightarrow \{Assignment\}$$
$$ [[\ p_1 = p_2\ ]]_\Delta = [[\ p_1\ ]]_\Delta \dot{\cap} [[\ p_2\ ]]_\Delta $$

$$ S\ \dot{\cap}\ T = \{\ \Gamma \cup \Pi : V_\Gamma \in S\ \text{and}\ V_\Pi \in T\ \text{and}\  \text{compatible}(\Gamma,\Pi)\} $$
$$ S\ \triangleleft\ \Sigma = \{\ V_{\Gamma\ \cup\ \Pi} | V_\Gamma \in S\ and\ \Pi \in \Sigma\ \text{such that}\ \text{compatible}(\Gamma,\Pi) \} $$
$$ \text{compatible}(\Gamma,\Pi) = \forall X \in \text{dom}(\Gamma) \cap \text{dom}(\Pi). \Gamma(X) = \Pi(X) $$

I'm a little sloppy with notation above for the meaning of queries. But the central idea is that the value of an equality statement is a (set of) variable assignment that makes the two sides equal.

# Semantics of Set constructs
We extend the syntax of patterns to include two new constructs:
$$ P ::= \dots\ |\ \text{elements}(p)\ |\ \text{all}(p) $$

### Notation for sets in Angle

We use curly braces with a bar to mean set values in Angle. This is to separate them from the set of results on the "meta" level.

Example: below are two result, one containing a set with one element and that element is the `nat` 1 and the other is a set containing the element `nat` 2.

$$ \{ \ \{| \text{1}  |\} \ ,\ \{| \text{2} |\} \} $$

The general idea is that $\text{elements}$ takes a set as an argument and returns each elements in the set as a separate query. $\text{all}$ does the reverse. It takes all the query results of its argument and makes them into a single result which is a set containing all the results of the query.

Formally, the semantics is as follows:
$$ [[\ elements(p)\ ]]_\Delta = \{ v_{\Gamma} : set_\Gamma \in [[\ p\ ]]_\Delta, v \in set \} $$
$$ [[\ \text{all}(p)\ ]]_\Delta = \{\ \{| \ v\  : \ v_\Gamma \in [[\ p\ ]]_\Delta |\}_{\cap \Gamma} \ \} $$
