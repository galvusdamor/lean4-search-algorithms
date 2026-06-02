
.PHONY: build doc show-doc clean

build:
	lake build

doc:
	cd docbuild && lake -Kenv=dev build SearchAlgorithms:docs
	cat docbuild/docs/additional.css >> docbuild/.lake/build/doc/style.css

show-doc: doc
	(sleep 2 && firefox http://127.0.0.1:8000/SearchAlgorithms.html) &
	cd docbuild/.lake/build/doc && python -m http.server --bind 127.0.0.1

clean:
	rm -rf .first-run-done lake-packages .lake build lakefile.olean

# Dependency SearchAlgorithms

LEAN_FILES := $(wildcard SearchAlgorithms/*.lean)

dependencies.svg: dependencies.dot
	dot -Tsvg dependencies.dot > $@

dependencies.dot: $(LEAN_FILES)
	@echo "digraph {" > $@
	@$(foreach file, $^ ,\
		if grep -q "sorry" "$(file)"; then \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))?\", color="red", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		else \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))✓\", color="green", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		fi;)
	@(grep -nr "import SearchAlgorithms" SearchAlgorithms/*.lean | awk -F '[./]' '{print $$4 " -> " $$2}') >> $@
	@echo "}" >> $@
