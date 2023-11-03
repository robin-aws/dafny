
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=obj/systemModulePopulator.cs
GENERATED_SYSTEM_MODULE_TARGET=DafnyRuntimeSystemModule.cs

GENERATED_STDLIBS_SOURCE=obj/DafnyStandardLibraries.cs
GENERATED_STDLIBS_TARGET=DafnyStandardLibraries.cs

test: check-system-module check-stdlibs

build-system-module:
	$(DAFNY) translate cs --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --system-module:OmitAllOtherModules systemModulePopulator.dfy --output:obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)
	
build-stdlibs:
	$(DAFNY) translate cs --no-verify --use-basename-for-filename --optimize-erasable-datatype-wrapper:false --default-module:Omit ../DafnyStandardLibraries/src/dfyconfig.toml --output:obj/DafnyStandardLibraries.cs

check-stdlibs: build-stdlibs
	diff $(GENERATED_STDLIBS_SOURCE) $(GENERATED_STDLIBS_TARGET)

update-stdlibs: build-stdlibs
	cp $(GENERATED_STDLIBS_SOURCE) $(GENERATED_STDLIBS_TARGET)

	