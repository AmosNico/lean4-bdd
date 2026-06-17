BDD_LEAN_FILES := $(shell find Bdd -name '*.lean')

BASE = https://eshelyaron.com/man/lean4-bdd/Bdd/

dependencies.svg: dependencies.dot
	dot -Tsvg dependencies.dot > $@

dependencies.dot: $(BDD_LEAN_FILES)
	@echo "digraph {" > $@
	@$(foreach file, $^ ,\
		if grep -q "sorry" "$(file)"; then \
			echo "\"$(patsubst Bdd/%.lean,%,$(file))\" [ label = \"$(patsubst Bdd/%.lean,%,$(file))\", color="red", href = \"$(BASE)$(patsubst Bdd/%.lean,%,$(file)).html\" ]" >> $@; \
		else \
			echo "\"$(patsubst Bdd/%.lean,%,$(file))\" [ label = \"$(patsubst Bdd/%.lean,%,$(file))\", color="green", href = \"$(BASE)$(patsubst Bdd/%.lean,%,$(file)).html\" ]" >> $@; \
		fi;)
	@(grep -rn --include='*.lean' "^import Bdd" Bdd | awk -F: '{ imp=$$1; sub(/^Bdd\//,"",imp); sub(/\.lean$$/,"",imp); mod=$$3; sub(/^import Bdd\.?/,"",mod); gsub(/\./,"/",mod); if (mod != "" && mod != imp) print "\"" mod "\" -> \"" imp "\"" }') >> $@
	@echo "}" >> $@

doc:
	cd docbuild && lake build Bdd:docs
