build: TechnicalLemmas.vo SyntaxTests.vo ProofSystemTests.vo ModelTests.vo Theorems.vo 

Theorems.vo :  Monotonicity.vo MonotonicityBelief.vo Theorems.v
	coqc Theorems.v

MonotonicityBelief.vo : TechnicalLemmasBelief.vo MonotonicityBelief.v
	coqc MonotonicityBelief.v

Monotonicity.vo : TechnicalLemmas.vo Monotonicity.v
	coqc Monotonicity.v

TechnicalLemmasBelief.vo : Belief.vo TechnicalLemmasBelief.v
	coqc TechnicalLemmasBelief.v

TechnicalLemmas.vo: Model.vo ProofSystem.vo TechnicalLemmas.v
	coqc TechnicalLemmas.v

ModelTests.vo: Model.vo ModelTests.v
	coqc ModelTests.v

Belief.vo: FirstOrder.vo Belief.v
	coqc Belief.v

Model.vo: FirstOrder.vo Model.v
	coqc Model.v

FirstOrder.vo: Syntax.vo FirstOrder.v
	coqc FirstOrder.v

ProofSystemTests.vo: ProofSystem.vo ProofSystemTests.v
	coqc ProofSystemTests.v

ProofSystem.vo: Syntax.vo ProofSystem.v
	coqc ProofSystem.v

SyntaxTests.vo: Syntax.vo SyntaxTests.v
	coqc SyntaxTests.v

Syntax.vo: Syntax.v
	coqc Syntax.v

clean:
	rm -f *.vo *.glob *.tar.gz

doc: Syntax.tex Model.tex ProofSystem.tex

Syntax.tex: Syntax.vo Syntax.v
	coqdoc --latex --body-only --no-externals -o Syntax.tex Syntax.v

Model.tex: Model.vo Model.v
	coqdoc --latex --body-only --no-externals -o Model.tex Model.v

ProofSystem.tex: ProofSystem.vo ProofSystem.v
	coqdoc --latex --body-only --no-externals -o ProofSystem.tex ProofSystem.v

dist: clean
	cd ..; \
	tar czf focal.tar.gz focal/*.v focal/README focal/Makefile; \
	mv focal.tar.gz focal; \
	cd focal
