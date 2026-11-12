import Lake
open Lake DSL

-- Pin the matching Lean 4.35 stable dependency stack.
require verso from git "https://github.com/leanprover/verso"@"v4.35.0"
require «verso-slides» from git "https://github.com/leanprover/verso-slides"@"v4.35.0"
-- Side-by-side nodes need `SubVerso.Module.findDecl?` (eric-vergo/subverso
-- `feat/declaration-source`, proposed upstream). Return to the upstream tag once
-- it is released there.
require subverso from git "https://github.com/eric-vergo/subverso"@"feat/declaration-source"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.116"
require lean_vir from git "https://github.com/ejgallego/lean-vir"@"225218e18a3ae554acc571a93aab484453d857a6"

package VersoBlueprint where
  leanOptions := #[⟨`experimental.module, true⟩]

input_dir embeddedBlueprintAssets where
  path := "src/VersoBlueprint"
  text := true
  filter := .extension <| .mem #["css", "js", "mjs"]

input_file blueprintMathJs where
  path := "static-web/math.js"
  text := true

input_file mathLintWorkerJs where
  path := "static-web/katex-lint.mjs"
  text := true

-- The graph's browser libraries, shipped with every site (static-web/vendor/README.md).
input_dir vendoredWebAssets where
  path := "static-web/vendor"
  text := true
  filter := .extension <| .mem #["js"]

-- Optional VIR resource API; neither the core library nor generator imports it.
lean_lib VersoBlueprintVir where
  srcDir := "src"
  roots := #[`VersoBlueprintVir]

lean_lib VersoBlueprintVirClientTests where
  srcDir := "tests"
  roots := #[`VersoBlueprintVirClientTests.Program]

lean_lib VersoBlueprintVirClientResources where
  srcDir := "tests"
  roots := #[`VersoBlueprintVirClientTests.Resources]
  needs := #[`+VersoBlueprintVirClientTests.Program:virResourcePack]

lean_exe «vir-client-example» where
  srcDir := "tests"
  root := `VirClientExampleMain

-- Blueprint core library.
@[default_target]
lean_lib VersoBlueprint where
  srcDir := "src"
  roots := #[`VersoBlueprint]
  precompileModules := true
  needs := #[embeddedBlueprintAssets, blueprintMathJs, mathLintWorkerJs, vendoredWebAssets]

@[default_target]
lean_exe «vbp» where
  root := `VersoBlueprint.VbpMain
  srcDir := "src"
  supportInterpreter := true

@[default_target, test_driver]
lean_lib VersoBlueprintTests where
  srcDir := "tests"
  roots := #[
    `VersoBlueprintTests.Blueprint.Support,
    `VersoBlueprintTests.BlueprintAssets,
    `VersoBlueprintTests.BlueprintContributions,
    `VersoBlueprintTests.BlueprintImportedContributions,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingProofs,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingProofsReverse,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingStatements,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingMetadata,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingMarkup,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingRust,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingIntents,
    `VersoBlueprintTests.BlueprintImportedContributions.ConflictingIntentsReverse,
    `VersoBlueprintTests.BlueprintImportedContributions.AuthorityForward,
    `VersoBlueprintTests.BlueprintImportedContributions.AuthorityReverse,
    `VersoBlueprintTests.BlueprintAutoDeps,
    `VersoBlueprintTests.BlueprintAttribute,
    `VersoBlueprintTests.BlueprintAttribute.OrderRoundtrip,
    `VersoBlueprintTests.BlueprintAttributeRendering,
    `VersoBlueprintTests.BlueprintPlacementContracts,
    `VersoBlueprintTests.BlueprintAttributeLateRendering,
    `VersoBlueprintTests.BlueprintBlockFolding,
    `VersoBlueprintTests.BlueprintCodeRenderMatrix,
    `VersoBlueprintTests.BlueprintDarkTheme,
    `VersoBlueprintTests.BlueprintDocstringReferences,
    `VersoBlueprintTests.BlueprintImportedDuplicates.Direct,
    `VersoBlueprintTests.BlueprintImportedDuplicates.ProviderA,
    `VersoBlueprintTests.BlueprintImportedDuplicates.ProviderB,
    `VersoBlueprintTests.BlueprintImportedDuplicates.Reexport,
    `VersoBlueprintTests.BlueprintImportedDuplicates.Transitive,
    `VersoBlueprintTests.BlueprintExternalHeadingStatus,
    `VersoBlueprintTests.BlueprintGraft,
    `VersoBlueprintTests.BlueprintGraph,
    `VersoBlueprintTests.BlueprintHeaderExtras,
    `VersoBlueprintTests.BlueprintInformal,
    `VersoBlueprintTests.BlueprintProofLeanRefs,
    `VersoBlueprintTests.BlueprintProofLeanRefs.Roundtrip,
    `VersoBlueprintTests.BlueprintInlinePrecision,
    `VersoBlueprintTests.BlueprintLeanSourceAnchors,
    `VersoBlueprintTests.BlueprintLinkHover,
    `VersoBlueprintTests.BlueprintMainWrapper,
    `VersoBlueprintTests.BlueprintPreviewResources,
    `VersoBlueprintTests.BlueprintMathLint,
    `VersoBlueprintTests.BlueprintMetadataPanel,
    `VersoBlueprintTests.BlueprintIssueUrl,
    `VersoBlueprintTests.BlueprintNumbering,
    `VersoBlueprintTests.BlueprintSlides,
    `VersoBlueprintTests.BlueprintPreviewPanels,
    `VersoBlueprintTests.BlueprintPreviewSchema,
    `VersoBlueprintTests.BlueprintPreviewSource,
    `VersoBlueprintTests.BlueprintPreviewWiring,
    `VersoBlueprintTests.BlueprintNodeView,
    `VersoBlueprintTests.BlueprintSideBySide,
    `VersoBlueprintTests.BlueprintSidebar,
    `VersoBlueprintTests.BlueprintSource,
    `VersoBlueprintTests.SorryImport.Provider,
    `VersoBlueprintTests.SorryImport.Consumer,
    `VersoBlueprintTests.SorryImport.Classification,
    `VersoBlueprintTests.SorryImport.PrivateBoundary,
    `VersoBlueprintTests.SorryImport.PrivateProvider,
    `VersoBlueprintTests.SorryImport.Captured,
    `VersoBlueprintTests.SorryImport.CapturedConsumer,
    `VersoBlueprintTests.BlueprintSourceIdentity,
    `VersoBlueprintTests.BlueprintRustCode,
    `VersoBlueprintTests.BlueprintSummaryLinks,
    `VersoBlueprintTests.BlueprintSummaryStatus,
    `VersoBlueprintTests.BlueprintTeXCleanup,
    `VersoBlueprintTests.BlueprintTexMacros,
    `VersoBlueprintTests.BlueprintExternalMarkup,
    `VersoBlueprintTests.BlueprintWorkQueue,
    `VersoBlueprintTests.ExternalDeclRender,
    `VersoBlueprintTests.ResidentBuild,
    `VersoBlueprintTests.RuntimeCache,
    `VersoBlueprintTests.SerializedExtension,
    `VersoBlueprintTests.TestBlueprintRegistryMeta,
    `VersoBlueprintTests.TestBlueprintRegistryChecks,
    `VersoBlueprintTests.TestBlueprintRegistryCoverage,
    `VersoBlueprintTests.Vbp
  ]

lean_lib VersoBlueprintTestDocs where
  srcDir := "tests"
  roots := #[`VersoBlueprintTests.TestBlueprintRegistry]

lean_exe «blueprint-test-docs» where
  root := `BlueprintTestDocsMain
  srcDir := "tests"
  supportInterpreter := true

-- Optional native scaling probe; not part of normal builds or the test driver.
lean_exe «blueprint-contribution-bench» where
  root := `BlueprintContributionBench
  srcDir := "tests"
  moreLeancArgs := #["-O3"]
