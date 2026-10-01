//  * (c) Copyright 2026 Bruno Bentzen. All rights reserved.
//  * Released under Apache 2.0 license as described in the file LICENSE.
//  * Desc: Monitors when a .cube file is saved, runs the compiler binary, and 
//          interprets standard OCaml error messages via regular expressions
//          to highlight lines in VS Code.
 

import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as path from 'path';
import * as fs from 'fs';

let diagnosticCollection: vscode.DiagnosticCollection;

// Dictionary mapping abbreviations to Unicode symbols
const UNICODE_ABBREVIATIONS: { [key: string]: string } = {
    'rightarrow': '→', 'to': '→', 'leftrightarrow': '↔', 'iff': '↔',
    'lambda': 'λ', 'let': 'λ',
    'neg': '¬',
    'Pi': 'Π',
    'Sigma': 'Σ',
    'times': '×',
    'nat': 'ℕ', 'int': 'ℤ', 'rat': 'ℚ', 'real': 'ℝ',
    'I': '𝕀',
    'inv': '⁻¹', 'comp': '·',
    'forall': '∀', 'exists': '∃', 'and': '∧', 'or': '∨', 'vdash': '⊢',
    'in': '∈', 'notin': '∉', 'subset': '⊂', 'subseteq': '⊆', 'supset': '⊃', 'supseteq': '⊇', 'emptyset': '∅', 'cup': '∪', 'cap': '∩',
    'Rightarrow': '⇒', 'Leftrightarrow': '⇔',
    '_0': '₀', '_1': '₁', '_2': '₂', '_3': '₃', '_4': '₄', '_5': '₅', '_6': '₆', '_7': '₇', '_8': '₈', '_9': '₉',
    '^0': '⁰', '^1': '¹', '^2': '²', '^3': '³', '^4': '⁴', '^5': '⁵', '^6': '⁶', '^7': '⁷', '^8': '⁸', '^9': '⁹',
    'alpha': 'α', 'beta': 'β', 'gamma': 'γ', 'delta': 'δ', 'epsilon': 'ε', 'zeta': 'ζ', 'eta': 'η', 'theta': 'θ',
    'iota': 'ι', 'kappa': 'κ', 'mu': 'μ', 'nu': 'ν', 'xi': 'ξ', 'omicron': 'ο', 'pi': 'π',
    'rho': 'ρ', 'sigma': 'σ', 'tau': 'τ', 'upsilon': 'υ', 'phi': 'φ', 'chi': 'χ', 'psi': 'ψ', 'omega': 'ω',
    'Gamma': 'Γ', 'Delta': 'Δ', 'Theta': 'Θ', 'Lambda': 'Λ', 'Xi': 'Ξ', 'Upsilon': 'Υ', 'Phi': 'Φ', 'Psi': 'Ψ', 'Omega': 'Ω',
    '^+': '⁺', '^-': '⁻', '^=': '⁼', '^(': '⁽', '^)': '⁾',
    'ell': 'ℓ', 'mathcalA': '𝓐', 'mathcalB': '𝓑', 'mathcalC': '𝓒', 'mathcalD': '𝓓', 'mathcalE': '𝓔', 'mathcalF': '𝓕', 'mathcalG': '𝓖',
    'mathcalH': '𝓗', 'mathcalI': '𝓘', 'mathcalJ': '𝓙', 'mathcalK': '𝓚', 'mathcalL': '𝓛', 'mathcalM': '𝓜', 'mathcalN': '𝓝',
    'mathcalO': '𝓞', 'mathcalP': '𝓟', 'mathcalQ': '𝓠', 'mathcalR': '𝓡', 'mathcalS': '𝓢', 'mathcalT': '𝓣', 'mathcalU': '𝓤',
    'mathcalV': '𝓥', 'mathcalW': '𝓦', 'mathcalX': '𝓧', 'mathcalY': '𝓨', 'mathcalZ': '𝓩',
    'infty': '∞', 'partial': '∂', 'nabla': '∇', 'angle': '∠', 'perp': '⊥', 'therefore': '∴', 'because': '∵',
    'approx': '≈', 'cong': '≅', 'equiv': '≡', 'sim': '∼', 'simeq': '≃', 'asymp': '≍',
    'leq': '≤', 'geq': '≥', 'll': '≪', 'gg': '≫', 'prec': '≺', 'succ': '≻',
    'subsetneq': '⊊', 'supsetneq': '⊋', 
    '+-': '±', '-+': '∓',
    // Add more abbreviations and symbols as needed
};

type CubeSymbol = {
    name: string;
    kind: string;
    file: string;
    line: number;
    col_start: number;
    col_end: number;
};

function getCubeExecutablePath(): string {
    const config = vscode.workspace.getConfiguration('cube');
    let cubePath = config.get<string>('executablePath') || 'cube';

    if (cubePath === 'cube' && vscode.workspace.workspaceFolders) {
        const workspaceDir = vscode.workspace.workspaceFolders[0].uri.fsPath;
        const siblingCubeRoot = path.resolve(workspaceDir, '..', 'cube');

        const possiblePaths = [
            path.join(siblingCubeRoot, 'cube'),
            path.join(siblingCubeRoot, '_build', 'default', 'src', 'main.exe'),
            path.join(siblingCubeRoot, '_build', 'default', 'src', 'cube.exe'),
            path.join(siblingCubeRoot, '_build', 'default', 'bin', 'main.exe')
        ];

        for (const p of possiblePaths) {
            if (fs.existsSync(p)) {
                cubePath = p;
                break;
            }
        }
    }

    return cubePath;
}

async function loadCubeSymbolsForFile(filePath: string): Promise<CubeSymbol[]> {
    const cubePath = getCubeExecutablePath();

    return new Promise((resolve) => {
        exec(`"${cubePath}" --dump-symbols "${filePath}"`, (error, stdout, stderr) => {
            const output = (stdout + '\n' + stderr).trim();
            if (error && !output) {
                resolve([]);
                return;
            }

            if (!output) {
                resolve([]);
                return;
            }

            try {
                const parsed = JSON.parse(output);
                if (!Array.isArray(parsed)) {
                    resolve([]);
                    return;
                }
                resolve(parsed as CubeSymbol[]);
            } catch {
                resolve([]);
            }
        });
    });
}

async function collectCubeSymbolsForFile(filePath: string, visited = new Set<string>()): Promise<CubeSymbol[]> {
    if (visited.has(filePath)) {
        return [];
    }
    visited.add(filePath);

    const symbols = await loadCubeSymbolsForFile(filePath);
    try {
        const source = fs.readFileSync(filePath, 'utf8');
        const importRegex = /(^|\s)import\s+([^\r\n]+)/gm;
        let match: RegExpExecArray | null;

        while ((match = importRegex.exec(source)) !== null) {
            const importPath = (match[2] || '').trim();
            if (!importPath) {
                continue;
            }

            const resolved = path.resolve(path.dirname(filePath), importPath);
            if (fs.existsSync(resolved)) {
                const nested = await collectCubeSymbolsForFile(resolved, visited);
                symbols.push(...nested);
            }
        }
    } catch {
        // Ignore missing or unreadable imported files; the current file still contributes its own definitions.
    }

    return symbols;
}

async function findCubeDefinitionAtPosition(document: vscode.TextDocument, position: vscode.Position): Promise<vscode.Location | undefined> {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }

    const name = document.getText(range);
    if (!name) {
        return undefined;
    }

    const symbols = await collectCubeSymbolsForFile(document.uri.fsPath);
    const matches = symbols.filter((symbol) => symbol.name === name);
    if (matches.length === 0) {
        return undefined;
    }

    const symbol = matches[0];
    const targetUri = vscode.Uri.file(symbol.file);
    const line = Math.max(0, symbol.line - 1);
    const startColumn = Math.max(0, symbol.col_start);
    const endColumn = Math.max(startColumn, symbol.col_end);

    return new vscode.Location(targetUri, new vscode.Range(
        new vscode.Position(line, startColumn),
        new vscode.Position(line, endColumn)
    ));
}

export function activate(context: vscode.ExtensionContext) {
    diagnosticCollection = vscode.languages.createDiagnosticCollection('cube');
    context.subscriptions.push(diagnosticCollection);

    context.subscriptions.push(
        vscode.languages.registerDefinitionProvider('cube', {
            provideDefinition(document: vscode.TextDocument, position: vscode.Position) {
                return findCubeDefinitionAtPosition(document, position);
            }
        })
    );

    // 1. Diagnostics on Save
    context.subscriptions.push(
        vscode.workspace.onDidSaveTextDocument((document: vscode.TextDocument) => {
            if (document.languageId === 'cube') {
                runCubeDiagnostics(document);
            }
        })
    );

    // 2. Unicode Abbreviation Completion Provider
    const unicodeProvider = vscode.languages.registerCompletionItemProvider(
        'cube',
        {
            provideCompletionItems(document: vscode.TextDocument, position: vscode.Position) {
                const lineText = document.lineAt(position.line).text;
                const lineStartToCursor = lineText.substring(0, position.character);
                
                // Match a backslash followed by alphanumeric characters right before the cursor
                const match = lineStartToCursor.match(/\\(\w*)$/);
                if (!match) {
                    return [];
                }

                const typedPrefix = match[1]; // e.g., "to" if they typed "\to"
                const completionItems: vscode.CompletionItem[] = [];

                // Filter and build completion suggestions based on what was typed
                for (const [abbr, symbol] of Object.entries(UNICODE_ABBREVIATIONS)) {
                    if (abbr.startsWith(typedPrefix)) {
                        const item = new vscode.CompletionItem(`\\${abbr}`, vscode.CompletionItemKind.Text);
                        item.insertText = symbol;
                        item.detail = `Unicode: ${symbol}`;
                        item.documentation = new vscode.MarkdownString(`Replaces \\\`${abbr}\\\` with \`${symbol}\``);
                        
                        // Define the specific text range to replace (including the backslash)
                        const startCharacter = position.character - (typedPrefix.length + 1);
                        item.range = new vscode.Range(
                            new vscode.Position(position.line, startCharacter),
                            position
                        );
                        
                        // Optional: Sort items so exact matches pop up first
                        item.sortText = abbr === typedPrefix ? '0' : '1' + abbr;
                        
                        completionItems.push(item);
                    }
                }

                return completionItems;
            }
        },
        '\\' // Trigger the provider automatically whenever '\' is pressed
    );

    context.subscriptions.push(unicodeProvider);
}

function runCubeDiagnostics(document: vscode.TextDocument) {
    const config = vscode.workspace.getConfiguration('cube');
    let cubePath = config.get<string>('executablePath') || 'cube';

    if (cubePath === 'cube' && vscode.workspace.workspaceFolders) {
        const workspaceDir = vscode.workspace.workspaceFolders[0].uri.fsPath;
        const siblingCubeRoot = path.resolve(workspaceDir, '..', 'cube');
        
        const possiblePaths = [
            path.join(siblingCubeRoot, 'cube'),
            path.join(siblingCubeRoot, '_build', 'default', 'src', 'main.exe'),
            path.join(siblingCubeRoot, '_build', 'default', 'src', 'cube.exe'),
            path.join(siblingCubeRoot, '_build', 'default', 'bin', 'main.exe')
        ];

        for (const p of possiblePaths) {
            if (fs.existsSync(p)) {
                cubePath = p;
                break;
            }
        }
    }

    const filePath = document.uri.fsPath;
    diagnosticCollection.clear();

    exec(`"${cubePath}" "${filePath}"`, (error, stdout, stderr) => {
        const output = (stdout + "\n" + stderr).trim();
        const normalizedOutput = normalizeCubeOutput(output);
        const isCommandFailure = !!error;

        if (error && ((error as any).code === 127 || error.message.includes('ENOENT'))) {
            vscode.window.showErrorMessage(
                `Cube binary could not be located. Ensure it is compiled or set its absolute location via 'cube.executablePath' in your VS Code settings.`
            );
            return;
        }

        if (!normalizedOutput) return;

        const locatedRegex = /line\s+(\d+),\s+characters\s+(\d+)-(\d+):([\s\S]*)/i;
        const locatedMatch = normalizedOutput.match(locatedRegex);

        if (locatedMatch) {
            const line = parseInt(locatedMatch[1], 10) - 1;
            const startChar = parseInt(locatedMatch[2], 10);
            const endChar = parseInt(locatedMatch[3], 10);
            const message = locatedMatch[4].trim();
            const diagnosticMessage = /unexpected token variant/i.test(message)
                ? `Syntax Error:\n${message}`
                : message;

            createDiagnostic(document, line, startChar, endChar, diagnosticMessage, vscode.DiagnosticSeverity.Error);
            return;
        }

        const genericLineRegex = /(?:line|line:)\s+(\d+)/i;
        const lineMatch = normalizedOutput.match(genericLineRegex);

        if (lineMatch) {
            const line = parseInt(lineMatch[1], 10) - 1;
            const lineText = document.lineAt(line).text;
            createDiagnostic(document, line, 0, lineText.length, normalizedOutput, vscode.DiagnosticSeverity.Error);
            return;
        }

        createDiagnostic(
            document,
            0,
            0,
            10,
            isCommandFailure ? `Cube Error:\n${normalizedOutput}` : `Cube Output:\n${normalizedOutput}`,
            isCommandFailure ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Information
        );
    });
}

function normalizeCubeOutput(output: string): string {
    const failurePrefix = 'Fatal error: exception Failure("';

    if (output.startsWith(failurePrefix) && output.endsWith('")')) {
        const escaped = output.slice(failurePrefix.length, -2);
        
        const bytes: number[] = [];
        for (let i = 0; i < escaped.length; i++) {
            // Check for an escape sequence
            if (escaped[i] === '\\' && i + 1 < escaped.length) {
                const nextChar = escaped[i + 1];
                if (nextChar === 'n') { bytes.push(10); i++; continue; }
                if (nextChar === 'r') { bytes.push(13); i++; continue; }
                if (nextChar === 't') { bytes.push(9); i++; continue; }
                if (nextChar === '"') { bytes.push(34); i++; continue; }
                if (nextChar === '\\') { bytes.push(92); i++; continue; }
                
                // Handle OCaml's 3-digit decimal byte escapes (e.g., \226)
                if (i + 3 < escaped.length) {
                    const match = escaped.substring(i + 1, i + 4).match(/^[0-9]{3}$/);
                    if (match) {
                        bytes.push(parseInt(match[0], 10));
                        i += 3;
                        continue;
                    }
                }
            }
            
            // Handle regular characters
            const charCode = escaped.charCodeAt(i);
            if (charCode < 128) {
                bytes.push(charCode);
            } else {
                // Safely encode any unescaped non-ASCII characters to UTF-8 bytes
                const utf8Buffer = Buffer.from(escaped[i], 'utf-8');
                for (let j = 0; j < utf8Buffer.length; j++) {
                    bytes.push(utf8Buffer[j]);
                }
            }
        }
        
        // Decode the reconstructed byte array back into a UTF-8 string
        return Buffer.from(bytes).toString('utf-8');
    }

    return output;
}

function createDiagnostic(document: vscode.TextDocument, line: number, start: number, end: number, message: string, severity: vscode.DiagnosticSeverity) {
    const safeLine = Math.min(Math.max(0, line), document.lineCount - 1);
    const lineText = document.lineAt(safeLine).text;
    const safeEnd = Math.min(end, lineText.length);

    const range = new vscode.Range(
        new vscode.Position(safeLine, start),
        new vscode.Position(safeLine, safeEnd)
    );

    const diagnostic = new vscode.Diagnostic(
        range,
        message,
        severity
    );

    diagnosticCollection.set(document.uri, [diagnostic]);
}

export function deactivate() {}