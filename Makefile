.PHONY: build
build:
	./gradlew createJar

.PHONY: install
install:
	echo "installing to local probcli/lib folder:"
	cp build/libs/tlc4b-1.0.*.jar ../../prob_prolog/lib/TLC4B.jar 
