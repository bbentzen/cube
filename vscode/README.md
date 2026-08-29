# Cube VS Code Extension

We recommend using the cube-vscode extension for verification support.

## Installation

The Cube VS Code Extension extension will soon be available on the VS Code marketplace. Simply search for `bbentzen.cube-vscode` on the VS Code Extensions view and click on the Install buttom. Alternativelly, you can install the extension manually from source. To do this, assuming you have already cloned the cube repository, you can run:

```
$ cd cube-vscode
$ npm install
$ npm run compile
```

Now you can copy the folder to `~/.vscode/extensions`.


## Usage

You need a cube executable. Open any `.cube` file on VS Code. Once you see any highlighted code you can compile the file simply by saving it with `Ctrl+S`.

If you see a message "Cube binary cannot be located", this is most likely because you need to tell VS Code the exact path to your executable to compile the file. You need to open the Settings editor via File > Preferences > Settings menu or using the `Ctrl+,` shortcut, then and go to Extensions > Cube Configuration. Under Cube: Executable Path you should provide the full path of the executable on your computer. For example:

`/home/myusername/cube/_build/default/bin/main.exe`

### Features 

The Cube VS Code Extension extension supports syntax highlighting, snippet completion, bracket matching, bracket autoclosing, bracket autosurrounding, comment toggling (`Ctrl` + `/`), and various LaTeX-style abbreviations for Unicode characters, including

* λ as `\lambda` or `\let`

* → as `\rightarrow` or `\to`

* ↔ as `\leftrightarrow` or `\iff`

* ¬ as `\neg`

* Π as `\Pi`

* Σ as `\Sigma` 
 
* × as `\times`

* Σ as `\Sigma` 

* ℕ as `\nat` 

* 𝕀 as `\I` 

* ⁻¹ as `\inv`

* · as `\comp`

* ⊢ as `\vdash` 