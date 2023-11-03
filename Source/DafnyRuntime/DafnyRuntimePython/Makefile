
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-py/System_.py
GENERATED_SYSTEM_MODULE_TARGET=System_.py

GENERATED_STDLIBS_SOURCE=../obj/DafnyStandardLibraries-py
GENERATED_STDLIBS_TARGET=.

test: check-system-module check-stdlibs

build-system-module:
	$(DAFNY) translate py --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

build-stdlibs:
	$(DAFNY) translate py --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --default-module:Omit ../../DafnyStandardLibraries/src/dfyconfig.toml --output:../obj/DafnyStandardLibraries

check-stdlibs: build-stdlibs
	diff -r -x Makefile -x System_.py -x _dafny.py -x __main__.py $(GENERATED_STDLIBS_SOURCE) $(GENERATED_STDLIBS_TARGET)

update-stdlibs: build-stdlibs
	rsync -rt $(GENERATED_STDLIBS_SOURCE)/DafnyStdLibs* $(GENERATED_STDLIBS_TARGET)
