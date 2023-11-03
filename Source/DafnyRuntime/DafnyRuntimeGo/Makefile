
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-go/src/System_/System_.go
GENERATED_SYSTEM_MODULE_TARGET=System_/System_.go

GENERATED_STDLIBS_SOURCE=../obj/DafnyStandardLibraries-go/src
GENERATED_STDLIBS_TARGET=.

all: check-system-module check-stdlibs test

test:
	cd dafny &&	GO111MODULE=auto go test

build-system-module:
	$(DAFNY) translate go --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

build-stdlibs:
	$(DAFNY) translate go --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false ../../DafnyStandardLibraries/src/dfyconfig.toml --output:../obj/DafnyStandardLibraries
	rm $(GENERATED_STDLIBS_SOURCE)/DafnyStandardLibraries.go

check-stdlibs: build-stdlibs
	diff -r -x Makefile -x System_ -x dafny $(GENERATED_STDLIBS_SOURCE) $(GENERATED_STDLIBS_TARGET)

update-stdlibs: build-stdlibs
	rsync -rt $(GENERATED_STDLIBS_SOURCE)/DafnyStdLibs* $(GENERATED_STDLIBS_TARGET)
