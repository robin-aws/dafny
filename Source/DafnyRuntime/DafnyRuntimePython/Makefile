
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-py/System_.py
GENERATED_SYSTEM_MODULE_TARGET=System_.py

GENERATED_STDLIBS_SOURCE=../obj/DafnyStandardLibraries-py/DafnyStdLibs
GENERATED_STDLIBS_TARGET=DafnyStdLibs

all: check-system-module

build-system-module:
	$(DAFNY) translate py --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

build-stdlibs:
	$(DAFNY) translate py --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false ../../DafnyStandardLibraries/src/dfyconfig.toml --output:../obj/DafnyStandardLibraries

check-stdlibs: build-stdlibs
	diff $(GENERATED_STDLIBS_SOURCE).py $(GENERATED_STDLIBS_TARGET).py
	diff $(GENERATED_STDLIBS_SOURCE)_Functions.py $(GENERATED_STDLIBS_TARGET)_Functions.py
	diff $(GENERATED_STDLIBS_SOURCE)_Relations.py $(GENERATED_STDLIBS_TARGET)_Relations.py
	diff $(GENERATED_STDLIBS_SOURCE)_Wrappers.py $(GENERATED_STDLIBS_TARGET)_Wrappers.py

update-stdlibs: build-stdlibs
	cp $(GENERATED_STDLIBS_SOURCE).py $(GENERATED_STDLIBS_TARGET).py
	cp $(GENERATED_STDLIBS_SOURCE)_Functions.py $(GENERATED_STDLIBS_TARGET)_Functions.py
	cp $(GENERATED_STDLIBS_SOURCE)_Relations.py $(GENERATED_STDLIBS_TARGET)_Relations.py
	cp $(GENERATED_STDLIBS_SOURCE)_Wrappers.py $(GENERATED_STDLIBS_TARGET)_Wrappers.py
