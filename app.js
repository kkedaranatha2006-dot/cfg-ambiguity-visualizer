const PRESETS = {
  "ambiguous-expr": {
    grammar: "E -> E + E | E * E | ( E ) | id",
    input: "id + id * id"
  },
  "unambiguous-expr": {
    grammar: "E -> E + T | T\nT -> T * F | F\nF -> ( E ) | id",
    input: "id + id * id"
  },
  "dangling-else": {
    grammar: "S -> i E t S | i E t S e S | a\nE -> b",
    input: "i b t i b t a e a"
  },
  "palindrome": {
    grammar: "S -> a S a | b S b | a | b | ε",
    input: "a b a"
  }
};

// Parse text into structured CFG rules
function parseGrammar(text) {
  const lines = text.split("\n").map(l => l.trim()).filter(Boolean);
  const rules = [];
  const nonTerminals = new Set();
  let startSymbol = null;

  for (const line of lines) {
    const parts = line.split("->");
    if (parts.length !== 2) throw new Error(`Invalid rule format: "${line}". Use "A -> B C"`);
    const lhs = parts[0].trim();
    if (!lhs) throw new Error("Empty left-hand side in rule.");
    if (!startSymbol) startSymbol = lhs;
    nonTerminals.add(lhs);

    const alternatives = parts[1].split("|").map(alt => alt.trim());
    for (const alt of alternatives) {
      if (alt === "ε" || alt === "eps" || alt === "") {
        rules.push({ lhs, rhs: [] });
      } else {
        rules.push({ lhs, rhs: alt.split(/\s+/) });
      }
    }
  }

  if (!startSymbol) throw new Error("Please enter at least one production rule.");
  return { startSymbol, nonTerminals, rules };
}

// Earley Parser with Parse Forest Extraction (up to maxTrees)
function parseString(grammar, tokens, maxTrees = 6) {
  const { startSymbol, nonTerminals, rules } = grammar;
  const n = tokens.length;
  const chart = Array.from({ length: n + 1 }, () => []);
  const stateMap = Array.from({ length: n + 1 }, () => new Map());

  function addState(col, lhs, rhs, dot, start, backpointers) {
    const key = `${lhs}->${rhs.join(" ")}@${dot},${start}`;
    if (!stateMap[col].has(key)) {
      const state = { lhs, rhs, dot, start, derivations: [] };
      stateMap[col].set(key, state);
      chart[col].push(state);
    }
    const existing = stateMap[col].get(key);
    if (backpointers) {
      const bpSig = JSON.stringify(backpointers);
      if (!existing.derivations.some(d => JSON.stringify(d) === bpSig)) {
        existing.derivations.push(backpointers);
      }
    }
  }

  // Seed start rules
  for (const r of rules) {
    if (r.lhs === startSymbol) {
      addState(0, r.lhs, r.rhs, 0, 0, []);
    }
  }

  for (let i = 0; i <= n; i++) {
    let idx = 0;
    while (idx < chart[i].length) {
      const state = chart[i][idx++];
      const { lhs, rhs, dot, start } = state;

      if (dot < rhs.length) {
        const nextSym = rhs[dot];
        if (nonTerminals.has(nextSym)) {
          // Predictor
          for (const r of rules) {
            if (r.lhs === nextSym) {
              addState(i, r.lhs, r.rhs, 0, i, []);
            }
          }
        } else if (i < n && nextSym === tokens[i]) {
          // Scanner
          const leafNode = { symbol: nextSym, isTerminal: true, children: [] };
          for (const prevDeriv of (state.derivations.length ? state.derivations : [[]])) {
            addState(i + 1, lhs, rhs, dot + 1, start, [...prevDeriv, leafNode]);
          }
        }
      } else {
        // Completer
        for (const prev of chart[start]) {
          if (prev.dot < prev.rhs.length && prev.rhs[prev.dot] === lhs) {
            const completedSubtree = {
              symbol: lhs,
              isTerminal: false,
              stateRef: state
            };
            for (const prevDeriv of (prev.derivations.length ? prev.derivations : [[]])) {
              addState(i, prev.lhs, prev.rhs, prev.dot + 1, prev.start, [...prevDeriv, completedSubtree]);
            }
          }
        }
      }
    }
  }

  // Extract distinct concrete trees
  const acceptingStates = chart[n].filter(
    s => s.lhs === startSymbol && s.dot === s.rhs.length && s.start === 0
  );

  const visitedGuard = new Set();
  function expandState(state, depth = 0) {
    if (depth > 25) return []; // Prevent infinite epsilon cycles
    const results = [];
    for (const deriv of state.derivations) {
      if (deriv.length === 0) {
        results.push([{ symbol: "ε", isTerminal: true, children: [] }]);
        continue;
      }
      let combos = [[]];
      for (const item of deriv) {
        if (item.isTerminal) {
          combos = combos.map(c => [...c, item]);
        } else {
          const subTrees = expandState(item.stateRef, depth + 1);
          const nextCombos = [];
          for (const c of combos) {
            for (const st of subTrees) {
              nextCombos.push([...c, { symbol: item.symbol, isTerminal: false, children: st }]);
              if (nextCombos.length >= maxTrees) break;
            }
            if (nextCombos.length >= maxTrees) break;
          }
          combos = nextCombos;
        }
      }
      for (const c of combos) {
        results.push(c);
        if (results.length >= maxTrees) return results;
      }
    }
    return results;
  }

  const finalTrees = [];
  const seenTreeHashes = new Set();
  for (const acc of acceptingStates) {
    const childCombos = expandState(acc);
    for (const children of childCombos) {
      const tree = { symbol: startSymbol, isTerminal: false, children };
      const hash = JSON.stringify(tree);
      if (!seenTreeHashes.has(hash)) {
        seenTreeHashes.add(hash);
        finalTrees.push(tree);
        if (finalTrees.length >= maxTrees) return finalTrees;
      }
    }
  }
  return finalTrees;
}

// Compute Leftmost Derivation Steps
function getLeftmostDerivation(root) {
  let frontier = [root];
  const steps = [root.symbol];
  while (frontier.some(n => !n.isTerminal)) {
    const idx = frontier.findIndex(n => !n.isTerminal);
    const target = frontier[idx];
    const replacement = target.children.length ? target.children : [{ symbol: "ε", isTerminal: true, children: [] }];
    frontier = [...frontier.slice(0, idx), ...replacement, ...frontier.slice(idx + 1)];
    steps.push(frontier.map(n => n.symbol).filter(s => s !== "ε").join(" ") || "ε");
  }
  return steps.join(" ⇒ ");
}

// Render Hierarchical SVG Parse Tree
function renderTreeSVG(root) {
  const leafSpacing = 62;
  const levelHeight = 68;
  let leafIndex = 0;
  let maxDepth = 0;

  function assignCoords(node, depth = 0) {
    maxDepth = Math.max(maxDepth, depth);
    node.y = depth * levelHeight + 35;
    if (!node.children || node.children.length === 0) {
      node.x = leafIndex * leafSpacing + 45;
      leafIndex++;
    } else {
      node.children.forEach(c => assignCoords(c, depth + 1));
      const firstX = node.children[0].x;
      const lastX = node.children[node.children.length - 1].x;
      node.x = (firstX + lastX) / 2;
    }
  }

  assignCoords(root);
  const width = Math.max(260, leafIndex * leafSpacing + 40);
  const height = (maxDepth + 1) * levelHeight + 25;

  let edgesSVG = "";
  let nodesSVG = "";

  function drawNode(node) {
    if (node.children) {
      for (const child of node.children) {
        edgesSVG += `<line x1="${node.x}" y1="${node.y}" x2="${child.x}" y2="${child.y}" stroke="#64748b" stroke-width="2" />`;
        drawNode(child);
      }
    }
    if (node.isTerminal) {
      nodesSVG += `
        <g transform="translate(${node.x}, ${node.y})">
          <rect x="-22" y="-14" width="44" height="28" rx="6" fill="#065f46" stroke="#10b981" stroke-width="2" />
          <text text-anchor="middle" dy="5" fill="#ecfdf5" font-family="Consolas, monospace" font-size="13" font-weight="bold">${node.symbol}</text>
        </g>`;
    } else {
      nodesSVG += `
        <g transform="translate(${node.x}, ${node.y})">
          <circle r="18" fill="#1e3a8a" stroke="#3b82f6" stroke-width="2" />
          <text text-anchor="middle" dy="5" fill="#eff6ff" font-family="Segoe UI, sans-serif" font-size="13" font-weight="bold">${node.symbol}</text>
        </g>`;
    }
  }

  drawNode(root);
  return `<svg width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">${edgesSVG}${nodesSVG}</svg>`;
}

// UI Execution
function runAnalysis() {
  const banner = document.getElementById("status-banner");
  const container = document.getElementById("trees-container");
  container.innerHTML = "";

  try {
    const grammar = parseGrammar(document.getElementById("grammar-input").value);
    const rawInput = document.getElementById("string-input").value.trim();
    const tokens = rawInput === "" || rawInput === "ε" ? [] : rawInput.split(/\s+/);

    const trees = parseString(grammar, tokens, 4);

    if (trees.length === 0) {
      banner.className = "status-banner rejected";
      banner.innerHTML = `<strong>REJECTED:</strong> The string <code>"${rawInput || "ε"}"</code> cannot be derived from start symbol <code>${grammar.startSymbol}</code>.`;
      return;
    }

    if (trees.length === 1) {
      banner.className = "status-banner unambiguous";
      banner.innerHTML = `<strong>ACCEPTED (1 Parse Tree):</strong> No ambiguity detected for <code>"${rawInput || "ε"}"</code>.`;
    } else {
      banner.className = "status-banner ambiguous";
      banner.innerHTML = `<strong>AMBIGUOUS GRAMMAR PROVEN:</strong> Found <strong>${trees.length} distinct parse trees</strong> for <code>"${rawInput || "ε"}"</code>!`;
    }

    trees.forEach((tree, idx) => {
      const card = document.createElement("div");
      card.className = "tree-card";
      card.innerHTML = `
        <div class="tree-card-header">
          <span>Parse Tree #${idx + 1}</span>
          <span>Yield: ${rawInput || "ε"}</span>
        </div>
        <div class="svg-wrapper">${renderTreeSVG(tree)}</div>
        <div class="derivation-box">
          <strong>Leftmost Derivation:</strong><br/>${getLeftmostDerivation(tree)}
        </div>
      `;
      container.appendChild(card);
    });
  } catch (err) {
    banner.className = "status-banner rejected";
    banner.innerHTML = `<strong>Syntax Error:</strong> ${err.message}`;
  }
}

// Auto-Hunt Ambiguous Counterexample via BFS Expansion
function autoHuntAmbiguity() {
  const banner = document.getElementById("status-banner");
  try {
    const grammar = parseGrammar(document.getElementById("grammar-input").value);
    const queue = [[grammar.startSymbol]];
    const tested = new Set();
    let iterations = 0;

    while (queue.length > 0 && iterations < 400) {
      iterations++;
      const seq = queue.shift();
      const nonTermIdx = seq.findIndex(sym => grammar.nonTerminals.has(sym));

      if (nonTermIdx === -1) {
        const candidateStr = seq.join(" ");
        if (!tested.has(candidateStr)) {
          tested.add(candidateStr);
          const trees = parseString(grammar, seq, 2);
          if (trees.length >= 2) {
            document.getElementById("string-input").value = candidateStr;
            runAnalysis();
            return;
          }
        }
      } else if (seq.length <= 9) {
        const target = seq[nonTermIdx];
        for (const r of grammar.rules) {
          if (r.lhs === target) {
            queue.push([...seq.slice(0, nonTermIdx), ...r.rhs, ...seq.slice(nonTermIdx + 1)]);
          }
        }
      }
    }

    banner.className = "status-banner unambiguous";
    banner.innerHTML = `<strong>No ambiguity found</strong> across ${tested.size} generated strings (up to length 9). Grammar appears unambiguous!`;
  } catch (err) {
    banner.className = "status-banner rejected";
    banner.innerHTML = `<strong>Error:</strong> ${err.message}`;
  }
}

// Wire up buttons & presets
document.querySelectorAll(".btn-preset").forEach(btn => {
  btn.addEventListener("click", () => {
    document.querySelectorAll(".btn-preset").forEach(b => b.classList.remove("active"));
    btn.classList.add("active");
    const preset = PRESETS[btn.dataset.preset];
    document.getElementById("grammar-input").value = preset.grammar;
    document.getElementById("string-input").value = preset.input;
    runAnalysis();
  });
});

document.getElementById("parse-btn").addEventListener("click", runAnalysis);
document.getElementById("hunt-btn").addEventListener("click", autoHuntAmbiguity);

// Load default on startup
window.addEventListener("DOMContentLoaded", () => {
  document.getElementById("grammar-input").value = PRESETS["ambiguous-expr"].grammar;
  document.getElementById("string-input").value = PRESETS["ambiguous-expr"].input;
  runAnalysis();
});