
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-go/src/System_/System_.go
GENERATED_SYSTEM_MODULE_TARGET=System_/System_.go

GENERATED_STDLIBS_SOURCE=../obj/DafnyStandardLibraries-go/src/DafnyStdLibs
GENERATED_STDLIBS_TARGET=DafnyStdLibs

all: check-system-module test

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

check-stdlibs: build-stdlibs
	diff $(GENERATED_STDLIBS_SOURCE)/DafnyStdLibs.go $(GENERATED_STDLIBS_TARGET)/DafnyStdLibs.go
	diff $(GENERATED_STDLIBS_SOURCE)_Functions/DafnyStdLibs_Functions.go $(GENERATED_STDLIBS_TARGET)_Functions/DafnyStdLibs_Functions.go
	diff $(GENERATED_STDLIBS_SOURCE)_Relations/DafnyStdLibs_Relations.go $(GENERATED_STDLIBS_TARGET)_Relations/DafnyStdLibs_Relations.go
	diff $(GENERATED_STDLIBS_SOURCE)_Wrappers/DafnyStdLibs_Wrappers.go $(GENERATED_STDLIBS_TARGET)_Wrappers/DafnyStdLibs_Wrappers.go
    
update-stdlibs: build-stdlibs
	cp $(GENERATED_STDLIBS_SOURCE)/DafnyStdLibs.go $(GENERATED_STDLIBS_TARGET)/DafnyStdLibs.go
	cp $(GENERATED_STDLIBS_SOURCE)_Functions/DafnyStdLibs_Functions.go $(GENERATED_STDLIBS_TARGET)_Functions/DafnyStdLibs_Functions.go
	cp $(GENERATED_STDLIBS_SOURCE)_Relations/DafnyStdLibs_Relations.go $(GENERATED_STDLIBS_TARGET)_Relations/DafnyStdLibs_Relations.go
	cp $(GENERATED_STDLIBS_SOURCE)_Wrappers/DafnyStdLibs_Wrappers.go $(GENERATED_STDLIBS_TARGET)_Wrappers/DafnyStdLibs_Wrappers.go
