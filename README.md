# Isabelle/jEdit Refactoring Plugin

A plugin for Isabelle/jEdit that adds refactoring actions to the editor.

**Currently implemented:**
- Rename a constant, fact, locale, class or type across theory files
- Promote a `have` block to a top-level lemma
- Generalise two lemmas into one (anti-unification)
- Move lemmas to the weakest locale in which they hold


## Prerequisites

- Isabelle (tested on Isabelle2025-2), with `isabelle` on your `PATH`
- jEdit (bundled with Isabelle)

## Repository layout

### Source files
| File | Purpose |
|------|---------|
| `ROOT` | Declares the `Refactor` session, which loads the Isabelle/ML code |
| `build.sh` | Compiles and installs the plugin, and registers the repo as an Isabelle component |
| `src/isabelle/jedit/refactor.scala` | Dispatcher: maps action names to implementations (e.g. `Refactor.rename(view)`) |
| `src/isabelle/jedit/rename.scala` | Renaming |
| `src/isabelle/jedit/promote_have.scala` | `have` block promotion |
| `src/isabelle/jedit/anti_unify.scala` | Lemma generalisation |
| `src/isabelle/jedit/weaken_locale.scala` | Locale weakening |
| `src/isabelle/jedit/locale_block.scala` | Finds where to insert a lemma in a locale's `begin`/`end` block |
| `src/isabelle/jedit/edits.scala` | `Edit` type and functions for applying edits to buffers and text |
| `src/isabelle/jedit/headless_handler.scala` | Headless session lifecycle management |
| `src/isabelle/jedit/utils.scala` | Shared utilities: `MarkupUtils` (markup traversal, fact lookup), `JEditUtils` (UI helpers), `SessionUtils` (project resolution), `CommandUtils` (command iteration) |
| `src/isabelle/jedit/Refactor_Plugin.scala` | Core plugin class (`extends EditPlugin`) |
| `src/isabelle/jedit/Refactor_Setup.thy` | Loads the ML files below into Isabelle |
| `src/isabelle/jedit/au.ML` | Anti-unification (`anti_unify` query operation) |
| `src/isabelle/jedit/promote_have.ML` | Liftability checks (`check_liftable` and `chained_facts` query operations) |
| `src/isabelle/jedit/weaken_locale.ML` | Weakest-locale search (`weakest_locale` query operation) |
| `actions.xml` | Declares action IDs and the code that runs when they trigger |
| `refactor.props` | Human-readable action labels, shown in menus and the Shortcuts dialog |
| `plugin.props` | Plugin metadata and core class declaration |

### Build artifacts (generated, not present in repo)
| Path | Contents |
|------|---------|
| `classes/` | Compiled `.class` files |
| `jarroot/` | Staging directory for assembling the jar |
| `Isabelle_Refactor.jar` | Final plugin jar |

## Building

Run the build script to compile and install the plugin:
```bash
./build.sh
```

The script compiles the plugin, copies the jar into the jEdit plugins directory
of your current Isabelle installation, and registers this repository as an
Isabelle component so that the `Refactor` session is available to your theories.
If you move the repository, run the script again. To unregister it:
```bash
isabelle components -x /path/to/this/repo
```

## Usage

1. Build and install the plugin (see above).
2. Open Isabelle/jEdit.
3. Go to **Utilities --> Global Options --> Shortcuts**.
4. Search for the refactoring actions and bind them to keys.
5. `have` promotion, lemma generalisation and locale weakening ask the prover
   for information, so the theory you are working in must import
   `Refactor.Refactor_Setup`:
   ```
   theory Foo
     imports Main Refactor.Refactor_Setup
   begin
   ```
   If the theory belongs to a session with its own `ROOT` file, you may also want to add
   `sessions Refactor` to that session's entry.
6. Trigger an action with its shortcut:
   - **Rename:** place your cursor on a constant, fact, locale, class or type.
   - **Promote `have`:** place your cursor on a `have` command.
   - **Generalise lemmas:** choose two lemmas from the current theory when prompted.
   - **Weaken locale:** choose which of the listed lemmas in the current theory to move.
