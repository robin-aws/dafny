
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

test: check-binary test-examples check-examples check-format

#
# DafnyStandardLibraries.doo ("binary")
#
# Pre-built and checked-in like all other Dafny-built artifacts,
# so this just follows the same regenerate-and-diff idiom.
#

DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo

build-binary:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}

#
# Runtime tests
#
# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.
#

test-examples:
	$(DAFNY) build -t:lib examples/dfyconfig.toml --output:build/stdlibexamples.doo
	$(DAFNY) test -t:cs build/stdlibexamples.doo --standard-libraries examples/BoundedInts/NonDefault.cs --output:build/stdlibexamples
	$(DAFNY) test -t:java build/stdlibexamples.doo --standard-libraries examples/BoundedInts/Externs/NonDefault.java --output:build/stdlibexamples
	$(DAFNY) test -t:go build/stdlibexamples.doo --standard-libraries examples/BoundedInts/NonDefault.go --output:build/stdlibexamples
	$(DAFNY) test -t:py build/stdlibexamples.doo --standard-libraries examples/BoundedInts/NonDefault.py --output:build/stdlibexamples
	$(DAFNY) test -t:js build/stdlibexamples.doo --standard-libraries examples/BoundedInts/NonDefault.js --output:build/stdlibexamples

# Runs embedded tests in Markdown files
check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

#
# Dafny source code formatting
#

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

#
# Miscellaneous
#

update-all-runtimes:
	make -C ../DafnyRuntime update-stdlibs
	make -C ../DafnyRuntime/DafnyRuntimeJava update-stdlibs
	make -C ../DafnyRuntime/DafnyRuntimeJs update-stdlibs
	make -C ../DafnyRuntime/DafnyRuntimeGo update-stdlibs
	make -C ../DafnyRuntime/DafnyRuntimePython update-stdlibs

clean:
	rm -rf build
