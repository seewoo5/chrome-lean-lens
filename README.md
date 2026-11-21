# Lean Lens: Lean 4 hovers on GitHub

A Chrome and Firefox extension for reviewing **Lean 4** pull requests. Hover a name, a tactic or a term in a GitHub diff to see its type, docstring, and where it comes from, as you would in your editor. With a Lean backend running, [the InfoView](#the-InfoView) is displayed beside the diff, showing the goal wherever you click.

It works on GitHub's diff views (`/files` and `/changes`) and on file pages.

## Install

1. Clone this repository.
1. If you want [the InfoView](#the-InfoView), run `npm install` in the cloned folder. It fetches [`@leanprover/InfoView`](https://www.npmjs.com/package/@leanprover/InfoView) from NPM into `InfoView/vendor/`. Other functionality works without this step.
1. Open `chrome://extensions` and switch on **Developer mode**.
1. Click **Load unpacked** and select the cloned folder.
1. Open a Lean pull request, go to **Files changed**, and hover.

After pulling updates, run `npm install` again if you use the InfoView. Then click **Reload** on the extension's card and refresh the GitHub tab.

### Firefox

The code is the same; only the manifest differs. Build the Firefox copy with Node 20+:

```bash
npm install                      # for the InfoView; skip to build without the InfoView
node scripts/build-firefox.mjs
```

1. Open `about:debugging#/runtime/this-firefox` and click **Load Temporary Add-on…**.
2. Pick `dist/firefox/manifest.json`.
3. If hovers don't appear, open `about:addons` → Lean Lens → **Permissions** and allow access to `github.com` and the other sites listed (including `127.0.0.1` and `localhost` for [real Lean](#real-lean)).

A temporary add-on stays until Firefox quits, and its settings may go with it: paste the helper's token again after loading it anew. After pulling updates, run the build again and click **Reload** in `about:debugging`. `node scripts/build-firefox.mjs --zip` also packs `dist/lean-lens-firefox-<version>.zip` for submitting to addons.mozilla.org.

## Two kinds of hovers

| | Setup | What you get |
|---|---|---|
| **Estimated** | none | The extension reads the diff, the file and [Loogle](https://loogle.lean-lang.org/) and works out what Lean would show. |
| **Real Lean** | [the helper](#real-lean) | Lean itself runs on the pull request. Hovers are exactly Lean's, and tactics show their proof state. |

With the helper switched on, a tooltip says which one you are looking at.

## What a hover shows

- **Declarations** from Lean, Mathlib or the pull request itself: the signature as Lean prints it, the docstring, and a link to the docs or to the line in the PR.
- **Local variables and hypotheses**: their type, written or inferred (from `intro`, `obtain`, `rw … at h` and the like).
- **Terms**: hover a gap, a bracket or an operator to get the term there and its type.
- **Tactics**: their documentation.
- **Declaration keywords** (`theorem`, `lemma`, `def`, …): what is in force there, as `#where` prints it: the namespaces and sections, and the `open`, `variable`, `include`, `omit`, `universe` and `set_option` commands, each with its line. On a pull request, a declaration it adds also gets [placement hints](#outline-and-placement).
- **With real Lean**: the goals after each tactic, and Lean's errors and `#check` output.

Estimated hovers follow Lean's rules for scopes, `open`, dot notation and section variables. When a type can't be worked out, no tooltip appears; when several names fit, the tooltip lists them.

### Stepping through a proof

With real Lean, a tactic's tooltip shows what it changed, as Lean's InfoView does: in the goals **after** it, what is new is green; switch to **Before** to see what went away in red. Hypotheses are matched by name and goals by their `case`, so only the part of a type or target that changed is marked.

The ◀ ▶ buttons (or ← → once the tooltip is pinned) move to the previous or next tactic of the proof. Stepping pins the tooltip where it is, so the buttons stay under the pointer; the tactic is shaded in the diff, and the page scrolls when needed to show it beside the tooltip. Tactics come in the order they finish, as when moving through the text in the editor: a `rw`'s rules before the `rw`, the proof of a `have` before the `have`. A step that only repeats the one before it is left out.

### Outline and placement

The **Outline** button at the bottom right of a pull request's files (or a Lean file page) lists the file's declarations with their line numbers, together with the commands GitHub's symbol list leaves out: `namespace`, `section`, `end`, `open`, `variable`, `include`, `omit`, and `open … in`-style prefixes. Click a line number to go there; click a declaration to see what is in force at it.

On a pull request, the declarations it adds are marked **new**, and a ⚑ marks a hint where one might belong instead:

- it sits between two declarations that go together (`foo` and `foo'`);
- it is much more like a declaration elsewhere in the file than like its neighbours.

Similarity is read from names (their words, with duals such as `open`/`closed` and `left`/`right` counted as alike) and the constants their statements mention. It is a hint, not a rule. Both the outline and the hints come from the file's text, without Lean, so they work without the helper.

## Real Lean

The helper is a small program that has Lean run on the commit you are reading and hands the result to the extension. It works on any repository with a Lake project.

Lean can run in two places:

| | Your machine | A GitHub Codespace |
|---|---|---|
| Start with | `node helper/lean-lens-helper.mjs` | `node helper/lean-lens-helper.mjs --codespaces` |
| You need | Node 20+, `git`, [`elan`](https://github.com/leanprover/elan) | Node 20+, [`gh`](https://cli.github.com) |
| Disk used on your machine | about 3 GB per Lean version, 10 GB while a Mathlib project is in use | the results only |
| First run on a Mathlib project | minutes; about 80 seconds if you link a built checkout | about 6 minutes |
| Cost | none | your own Codespaces allowance |

### Set it up

1. Start the helper with one of the commands above. It prints an address and a token.
2. Open the extension's options (in Chrome, right-click its icon → **Options**; in Firefox, `about:addons` → Lean Lens → **Preferences**), switch on **Use the local helper**, and paste the address and token. They save as you type; **Test Connection** checks them.
3. On a pull request, hover any name and press **Run Lean** in the tooltip. The first time on a repository, the button asks you to allow it.

The tooltip shows the progress. When the run is done, hovers on those files are Lean's own. Results are kept, so they stay instant afterwards.

### On your machine

If you already have the project built, link your checkout. The helper then starts from a copy of it instead of downloading everything, and never touches the checkout itself:

```bash
node helper/lean-lens-helper.mjs --link owner/repo=/path/to/your/checkout
```

The helper keeps little on disk. A repository's copy and build are removed 30 minutes after its last run and when the helper stops; only the results stay. To remove everything else it keeps:

```bash
node helper/lean-lens-helper.mjs clean
```

### In a codespace

Sign `gh` in and let it use codespaces once:

```bash
gh auth refresh -h github.com -s codespace
```

Then start the helper with `--codespaces`. From there it does the rest:

- The first **Run Lean** on a repository creates a codespace on that repository, installs Lean in it and runs there. Hovering never creates one. The helper notes which codespace that is and uses that one from then on. A codespace an earlier version of the helper used is not used again (code could run in it without a sandbox): a new one is made. The old one is left as it is, since those versions took over a codespace by the name shown for it, so it may be one of yours; `codespaces` below lists it apart, with the `gh codespace delete -c <identifier>` that deletes it.
- Results are copied to your machine, so hovers keep working after the codespace stops.
- A codespace is stopped 30 minutes after its last run and when the helper stops. GitHub deletes it after a week unused.
- If your machine sleeps or loses its network for a short while, the run carries on and is picked up again.

A free GitHub account includes 120 core-hours a month, which is 60 hours of the two-core machine the helper asks for. There is one codespace per repository because GitHub's terms allow a codespace for work on the repository it was started on.

To see, stop or delete the codespaces the helper uses. These are the ones its settings name, by the identifier GitHub gave each; a codespace is never picked by the name shown for it, so your others are left alone, and so is one that another running helper made for a run without a sandbox. One an earlier version of the helper used is listed apart and never stopped or deleted by these commands. A codespace made with other settings (another `--cache` folder, another machine) is not among them: `gh codespace list` shows it, and GitHub deletes it a week after it was last used.

```bash
node helper/lean-lens-helper.mjs codespaces
node helper/lean-lens-helper.mjs codespaces --stop
node helper/lean-lens-helper.mjs codespaces --delete
```

### The InfoView

With the Lean helper switched on, an **InfoView** tab at the right edge of the page is shown. It contains Lean's InfoView: the tactic state, expected type, messages, and widgets at the position you last clicked.

The panel can be widened or narrowed by dragging its left edge, and hidden with **⟩**. Lean keeps running while it is hidden.

While the panel is open, hovers show at its bottom, under the InfoView, instead of in a tooltip beside the code: the type and docstring of what the pointer last rested on, estimated (and marked so) or Lean's own, as the tooltip would show them. Such a hover stays when the pointer moves on, so it can be read and scrolled; the next hover replaces it, **Esc** clears it, and the pin (or **Alt**) keeps it while the pointer rests elsewhere. Drag the line above it to share the panel's height differently. With the panel hidden, hovers are tooltips again.

The InfoView panel behaves differently than in the editor in the following cases:

- **Go to definition** (Ctrl-click a name) scrolls to the right line when the definition is in the pull request's files, or opens it on GitHub when it is elsewhere in the repository. Definitions in Lean core or an upstream package are not opened.
- **Suggestions** (`Try this: …`) cannot be inserted, as the page is not editable. Clicking one puts it in the clipboard.
- **Restart File** reads the file again and rebuilds the imports.

The Lean server stops when you press **Stop**, when the page is closed or moves to another commit, and after 30 minutes without use (`--tidy-after`). **Start Lean** brings it back.

### Safety

Running Lean on a pull request runs that pull request's code: Lean executes code while it elaborates a file, and `lake` runs the project's `lakefile`. So:

- **Lean never starts on its own.** It runs when you press **Run Lean** or **Start Lean**, and only on repositories you have allowed.
- **The helper answers only the extension.** It listens on `127.0.0.1` and requires its token.
- **The code runs in a sandbox**, on macOS (`sandbox-exec`) and on Linux ([bubblewrap](https://github.com/containers/bubblewrap), which a codespace has). It has no network except while fetching the project's dependencies, cannot read or change your files, and gets none of your environment. Where there is no working sandbox (on Linux, when bubblewrap is missing or may not run), Lean does not run.
- **In a codespace** the sandbox also keeps the code away from the codespace's GitHub token. Without a working sandbox nothing runs there either.

The sandbox guards against the obvious; it is not a guarantee. `--no-sandbox` turns it off, which a project with private dependencies needs. Lean then runs with your permissions. In a codespace, where the code could then change the codespace itself and use its GitHub token, each such run gets a new codespace, deleted when the run is over: slower, since Lean is set up afresh each time. The helper notes the identifier GitHub gives that codespace (in `codespaces/` in its cache folder) before starting anything in it, and deletes that one only, never one found by its name or repository. The InfoView needs Lean to stay running, so with `--no-sandbox` it is not offered in a codespace (only for repositories run on your machine with `--here`). If the helper stops before it can, the next start deletes what was noted and no running helper is using; failing all that, GitHub deletes it an hour after it stops.

Worth knowing about what you allow:

- **Allowing a repository allows every pull request to it**, from forks too. What runs is the code of the pull request's author, not of the repository's owners.
- **The click on Run Lean is checked in the GitHub tab.** A GitHub page that was itself taken over could allow a repository and start a run without one.
- **A project chooses its Lean.** Its `lean-toolchain` may name a release from any GitHub repository; the helper installs that with elan, and the project's code runs with it.
- **A Lean file can bring widgets**: JavaScript that the InfoView loads from Lean and runs in the browser. In Chrome they run in a frame of their own, which has no network and reaches neither the extension nor the page on GitHub. In Firefox, which has no such frames, they are not run, and a widget shows an error in its place.

### Good to know

- A tactic shows the goals **after** it, and what it changed. The goals before the first tactic of a proof nested in another (`have h : T := by simp`) are not in Lean's recorded data, so that one shows its goals without a diff.
- A tactic that contains another proof, such as `exact foo (by simp)`, shows no state of its own.
- Files that need much compiled from source are slow in a codespace's two cores. `--codespace-machine standardLinux32gb` asks for four, at twice the cost.
- A codespace is built from the repository's own dev container when it has one. If that setup fails, GitHub starts the codespace in recovery mode, where Lean can't run, and the helper says so. mathlib4 is such a case today: its setup runs out of disk. Run those repositories on your machine with `--here owner/repo`.
- GitHub stops a codespace that nobody has connected to for 30 minutes. The helper keeps a running job alive, but a machine asleep for longer loses the run.
- The InfoView keeps four files open in Lean's server. Clicking in a fifth closes the one opened least recently; clicking in that one again opens it anew.
- With `--codespaces`, The Lean server runs in the repository's codespace, and the helper here forwards the InfoView's messages.
- Tested with Lean 4.35, on macOS and in GitHub's default codespace image.

### Helper options

| Option | What it does |
|---|---|
| `--codespaces` | Run Lean in GitHub Codespaces instead of on this machine |
| `--link owner/repo=PATH` | Start from your own built checkout of a repository |
| `--allow owner/repo` | Allow a repository ahead of time |
| `--here owner/repo` | With `--codespaces`: run this repository on your machine all the same |
| `--keep-builds` | Keep builds between runs: faster next time, more disk |
| `--keep-codespaces` | Leave codespaces running when idle and when the helper stops (not with `--no-sandbox`, where each run's codespace is deleted) |
| `--tidy-after MINUTES` | How long an unused build or codespace stays (default 30) |
| `--port N` | Listen on another port (default 5326) |
| `--no-sandbox` | Run a project's code without the sandbox, with your permissions (without this, no sandbox means no run) |

`node helper/lean-lens-helper.mjs --help` lists the rest. The helper can also elaborate files without the extension:

```bash
node helper/lean-lens-helper.mjs run --repo owner/repo --sha <full commit hash> Path/To/File.lean
```

## Extension options

In Chrome, right-click the toolbar icon → **Options**. In Firefox, open `about:addons` → Lean Lens → **Preferences**. Changes save as you make them.

- **Hover delay** and **theme**
- **Sources** for estimated hovers: the PR's own declarations, Loogle, built-in tactic docs
- **File outline**: the Outline button and its placement hints
- **Real Lean**: the helper's address and token, with a **Test Connection** button, and whether to show the **Infoview** tab. The address and token are kept apart from the other settings, in storage of the extension's own that scripts in web pages cannot read or change. A browser that gives the extension no such storage that lasts keeps them until it closes, or only until it stops the extension's background (which browsers do after a short while without use); the options page says which, and they are pasted again after that.

## Development

```bash
node test/run_tests.js
```

The tests need no Lean installation. Many expected outputs are Lean's own hovers on the same code, and `test/demo_pr.html` imitates a GitHub diff for trying tooltips offline.

```
manifest.json     Manifest V3 configuration (Chrome)
package.json      The one dependency, @leanprover/InfoView, which `npm install` puts in InfoView/vendor/
scripts/          build-firefox.mjs: the Firefox copy in dist/firefox/, with its own manifest
                  build-InfoView.mjs: the InfoView's files from node_modules/, ready for the extension
background/       Service worker (an event page in Firefox): Loogle, caching, the helper's client
content/          Hover handling, the term engine, the PR scanner, the tooltip, goal diffs, the outline,
                  the InfoView's panel and its cursor
InfoView/         The pages in the panel: host (the InfoView's editor, which talks to the helper)
                  and frame (the InfoView itself)
options/, popup/  Settings page and toolbar popup
helper/           The helper: runs Lean (locally or in a codespace) and converts its output;
                  live.mjs keeps Lean's server running for the InfoView
test/             Tests, fixtures and the demo page
```
