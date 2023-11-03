
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator.js
GENERATED_SYSTEM_MODULE_TARGET=DafnyRuntimeSystemModule.js

GENERATED_STDLIBS_SOURCE=obj/DafnyStandardLibraries.js
GENERATED_STDLIBS_TARGET=DafnyStandardLibraries.js

all: check-system-module

build-system-module:
	$(DAFNY) translate js --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

build-stdlibs:
	$(DAFNY) translate js --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false ../../DafnyStandardLibraries/src/dfyconfig.toml --output:../obj/DafnyStandardLibraries

check-stdlibs: build-stdlibs
	diff $(GENERATED_STDLIBS_SOURCE) $(GENERATED_STDLIBS_TARGET)

update-stdlibs: build-stdlibs
	cp $(GENERATED_STDLIBS_SOURCE) $(GENERATED_STDLIBS_TARGET)
