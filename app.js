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

// Global state for Step-by-Step Playback
let currentAnalysis = {
  trees: [],
  timelines: [], // Each timeline is an array of step objects for that tree
  currentStep: 0,
  maxSteps: 0,
  autoPlayTimer: null
};

// Parse text into structured CFG rules + Formal 4-Tuple (V, T, R, S)
function parseGrammar(text) {
  const lines = text.split("\n").map(l => l.trim()).filter(Boolean);
  const rules = [];
  const nonTerminals = new Set();
  const allSymbols = new Set();
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
        const rhsTokens = alt.split(/\s+/);
        rhsTokens.forEach(tok => allSymbols.add(tok));
        rules.push({ lhs, rhs: rhsTokens });
      }
    }
  }

  if (!startSymbol) throw new Error("Please enter at least one production rule.");

  const terminals = [...allSymbols].filter(sym => !nonTerminals.has(sym));
  return {
    startSymbol,
    nonTerminals,
    terminals,
    rules
  };
}

// Live update of the Formal Definition Box G = (V, Σ, R, S)
function updateFormalTupleDisplay() {
  try {
    const g = parseGrammar(document.getElementById("grammar-input").value);
    document.getElementById("tuple-v").textContent = `{ ${[...g.nonTerminals].join(", ")} }`;
    document.getElementById("tuple-t").textContent = g.terminals.length ? `{ ${g.terminals.join(", ")} }` : "{ ε }";
    document.getElementById("tuple-s").textContent = g.startSymbol;
    document.getElementById("tuple-r").textContent = `${g.rules.length} rules`;
  } catch {
    document.getElementById("tuple-v").textContent = "Syntax Error";
    document.getElementById("tuple-t").textContent = "-";
    document.getElementById("tuple-s").textContent = "-";
    document.getElementById("tuple-r").textContent = "-";
  }
}

// Earley Parser with Parse Forest Extraction
function parseString(grammar, tokens, maxTrees = 4) {
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

  for (const r of rules) {
    if (r.lhs === startSymbol) addState(0, r.lhs, r.rhs, 0, 0, []);
  }

  for (let i = 0; i <= n; i++) {
    let idx = 0;
    while (idx < chart[i].length) {
      const state = chart[i][idx++];
      const { lhs, rhs, dot, start } = state;

      if (dot < rhs.length) {
        const nextSym = rhs[dot];
        if (nonTerminals.has(nextSym)) {
          for (const r of rules) {
            if (r.lhs === nextSym) addState(i, r.lhs, r.rhs, 0, i, []);
          }
        } else if (i < n && nextSym === tokens[i]) {
          const leafNode = { symbol: nextSym, isTerminal: true, children: [] };
          for (const prevDeriv of (state.derivations.length ? state.derivations : [[]])) {
            addState(i + 1, lhs, rhs, dot + 1, start, [...prevDeriv, leafNode]);
          }
        }
      } else {
        for (const prev of chart[start]) {
          if (prev.dot < prev.rhs.length && prev.rhs[prev.dot] === lhs) {
            const completedSubtree = { symbol: lhs, isTerminal: false, stateRef: state };
            for (const prevDeriv of (prev.derivations.length ? prev.derivations : [[]])) {
              addState(i, prev.lhs, prev.rhs, prev.dot + 1, prev.start, [...prevDeriv, completedSubtree]);
            }
          }
        }
      }
    }
  }

  const acceptingStates = chart[n].filter(
    s => s.lhs === startSymbol && s.dot === s.rhs.length && s.start === 0
  );

  function expandState(state, depth = 0) {
    if (depth > 25) return [];
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

// Assign unique IDs to full tree and build Step-by-Step Leftmost Expansion Timeline
function buildStepTimeline(fullTree) {
  let idCounter = 1;
  function tagNodes(node) {
    const tagged = {
      id: idCounter++,
      symbol: node.symbol,
      isTerminal: node.isTerminal,
      children: (node.children || []).map(tagNodes)
    };
    return tagged;
  }
  const taggedRoot = tagNodes(fullTree);

  // Clone tree showing only expanded IDs, highlighting newly added IDs
  function projectTree(node, expandedSet, newlyAddedSet) {
    const isExpanded = expandedSet.has(node.id);
    const projected = {
      id: node.id,
      symbol: node.symbol,
      isTerminal: node.isTerminal,
      isNew: newlyAddedSet.has(node.id),
      isNextToExpand: false,
      children: []
    };
    if (isExpanded && node.children.length > 0) {
      projected.children = node.children.map(c => projectTree(c, expandedSet, newlyAddedSet));
    }
    return projected;
  }

  const expandedSet = new Set();
  const timeline = [];
  let frontier = [taggedRoot]; // Leftmost frontier of unexpanded nodes

  // Step 0: Start Symbol only
  const step0Tree = projectTree(taggedRoot, expandedSet, new Set([taggedRoot.id]));
  step0Tree.isNextToExpand = !taggedRoot.isTerminal;
  timeline.push({
    stepNum: 0,
    ruleApplied: `Start with root symbol (${taggedRoot.symbol})`,
    sententialForm: taggedRoot.symbol,
    treeSnapshot: step0Tree
  });

  let stepCount = 1;
  while (frontier.some(n => !n.isTerminal)) {
    const targetIdx = frontier.findIndex(n => !n.isTerminal);
    const targetNode = frontier[targetIdx];

    expandedSet.add(targetNode.id);
    const children = targetNode.children.length
      ? targetNode.children
      : [{ id: idCounter++, symbol: "ε", isTerminal: true, children: [] }];
    const newlyAddedSet = new Set(children.map(c => c.id));

    frontier = [
      ...frontier.slice(0, targetIdx),
      ...children,
      ...frontier.slice(targetIdx + 1)
    ];

    const rhsText = children.map(c => c.symbol).join(" ");
    const sentential = frontier.map(n => n.symbol).filter(s => s !== "ε").join(" ") || "ε";

    const snapshot = projectTree(taggedRoot, expandedSet, newlyAddedSet);
    // Mark next leftmost non-terminal that will expand on the following step
    const nextTarget = frontier.find(n => !n.isTerminal);
    if (nextTarget) {
      function markNext(n) {
        if (n.id === nextTarget.id) n.isNextToExpand = true;
        n.children.forEach(markNext);
      }
      markNext(snapshot);
    }

    timeline.push({
      stepNum: stepCount++,
      ruleApplied: `${targetNode.symbol} → ${rhsText}`,
      sententialForm: sentential,
      treeSnapshot: snapshot
    });
  }

  return timeline;
}

// Render Hierarchical SVG Parse Tree with Step Highlights
function renderTreeSVG(root) {
  const leafSpacing = 62;
  const levelHeight = 66;
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
        const edgeColor = child.isNew ? "#fbbf24" : "#64748b";
        const edgeWidth = child.isNew ? "2.8" : "2";
        edgesSVG += `<line x1="${node.x}" y1="${node.y}" x2="${child.x}" y2="${child.y}" stroke="${edgeColor}" stroke-width="${edgeWidth}" />`;
        drawNode(child);
      }
    }

    if (node.isTerminal) {
      const fill = node.isNew ? "#047857" : "#064e3b";
      const stroke = node.isNew ? "#fbbf24" : "#10b981";
      nodesSVG += `
        <g transform="translate(${node.x}, ${node.y})">
          <rect x="-22" y="-14" width="44" height="28" rx="6" fill="${fill}" stroke="${stroke}" stroke-width="2.5" />
          <text text-anchor="middle" dy="5" fill="#ecfdf5" font-family="Consolas, monospace" font-size="13" font-weight="bold">${node.symbol}</text>
        </g>`;
    } else {
      // Non-terminal: highlight Amber ring if it's the next leftmost variable to expand
      const fill = node.isNextToExpand ? "#78350f" : "#1e3a8a";
      const stroke = node.isNextToExpand ? "#fbbf24" : (node.isNew ? "#38bdf8" : "#3b82f6");
      const dash = node.isNextToExpand ? 'stroke-dasharray="4 2"' : "";
      nodesSVG += `
        <g transform="translate(${node.x}, ${node.y})">
          <circle r="18" fill="${fill}" stroke="${stroke}" stroke-width="2.5" ${dash} />
          <text text-anchor="middle" dy="5" fill="#eff6ff" font-family="Segoe UI, sans-serif" font-size="13" font-weight="bold">${node.symbol}</text>
        </g>`;
    }
  }

  drawNode(root);
  return `<svg width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">${edgesSVG}${nodesSVG}</svg>`;
}

// Render the current step across all trees
function renderCurrentStepView() {
  const container = document.getElementById("trees-container");
  container.innerHTML = "";

  const { timelines, currentStep, maxSteps } = currentAnalysis;
  document.getElementById("step-counter").textContent = `Step ${currentStep} / ${maxSteps}`;

  const descEl = document.getElementById("step-explanation");
  if (currentStep === 0) {
    descEl.textContent = "Initial state: Start Symbol (S) placed at the root. Click 'Next Step' to expand leftmost variable.";
  } else if (currentStep === maxSteps) {
    descEl.textContent = "Derivation complete! Compare the final tree structures side-by-side.";
  } else {
    descEl.textContent = "Gold dashed circle = next leftmost variable to expand; solid gold = newly derived nodes.";
  }

  document.getElementById("btn-first").disabled = currentStep === 0;
  document.getElementById("btn-prev").disabled = currentStep === 0;
  document.getElementById("btn-next").disabled = currentStep === maxSteps;
  document.getElementById("btn-last").disabled = currentStep === maxSteps;

  timelines.forEach((timeline, treeIdx) => {
    // Clamp step index in case one tree has slightly fewer steps than another
    const clampedIdx = Math.min(currentStep, timeline.length - 1);
    const frame = timeline[clampedIdx];

    const derivationTrail = timeline
      .slice(0, clampedIdx + 1)
      .map((f, i) =>
        i === clampedIdx
          ? `<span class="derivation-step-active">${f.sententialForm}</span>`
          : f.sententialForm
      )
      .join(" ⇒ ");

    const card = document.createElement("div");
    card.className = "tree-card";
    card.innerHTML = `
      <div class="tree-card-header">
        <span>Parse Tree #${treeIdx + 1}</span>
        <span>Step ${clampedIdx} of ${timeline.length - 1}</span>
      </div>
      <div class="rule-applied-pill">
        <strong>Action:</strong> ${frame.ruleApplied}
      </div>
      <div class="svg-wrapper">${renderTreeSVG(frame.treeSnapshot)}</div>
      <div class="derivation-box">
        <strong>Leftmost Derivation Trace:</strong><br/>${derivationTrail}
      </div>
    `;
    container.appendChild(card);
  });
}

function stopAutoPlay() {
  if (currentAnalysis.autoPlayTimer) {
    clearInterval(currentAnalysis.autoPlayTimer);
    currentAnalysis.autoPlayTimer = null;
    document.getElementById("btn-autoplay").textContent = "▶ Auto-Play";
  }
}

// Main Analysis Trigger
function runAnalysis(startAtComplete = false) {
  stopAutoPlay();
  updateFormalTupleDisplay();

  const banner = document.getElementById("status-banner");
  const playbackBar = document.getElementById("playback-bar");
  const container = document.getElementById("trees-container");
  container.innerHTML = "";

  try {
    const grammar = parseGrammar(document.getElementById("grammar-input").value);
    const rawInput = document.getElementById("string-input").value.trim();
    const tokens = rawInput === "" || rawInput === "ε" ? [] : rawInput.split(/\s+/);

    const trees = parseString(grammar, tokens, 4);

    if (trees.length === 0) {
      playbackBar.classList.add("hidden");
      banner.className = "status-banner rejected";
      banner.innerHTML = `<strong>REJECTED:</strong> The string <code>"${rawInput || "ε"}"</code> cannot be derived from start symbol <code>${grammar.startSymbol}</code>.`;
      return;
    }

    if (trees.length === 1) {
      banner.className = "status-banner unambiguous";
      banner.innerHTML = `<strong>ACCEPTED (1 Parse Tree):</strong> No ambiguity detected for <code>"${rawInput || "ε"}"</code>. Use the step controls below to trace its derivation.`;
    } else {
      banner.className = "status-banner ambiguous";
      banner.innerHTML = `<strong>AMBIGUOUS GRAMMAR PROVEN:</strong> Found <strong>${trees.length} distinct parse trees</strong> for <code>"${rawInput || "ε"}"</code>! Step through both trees simultaneously below to see where they diverge.`;
    }

    const timelines = trees.map(t => buildStepTimeline(t));
    const maxSteps = Math.max(...timelines.map(tl => tl.length - 1));

    currentAnalysis = {
      trees,
      timelines,
      currentStep: startAtComplete ? maxSteps : 0,
      maxSteps,
      autoPlayTimer: null
    };

    playbackBar.classList.remove("hidden");
    renderCurrentStepView();
  } catch (err) {
    playbackBar.classList.add("hidden");
    banner.className = "status-banner rejected";
    banner.innerHTML = `<strong>Syntax Error:</strong> ${err.message}`;
  }
}

// Visual Rule Builder "+ Add" Handler
document.getElementById("add-rule-btn").addEventListener("click", () => {
  const lhsInput = document.getElementById("new-lhs");
  const rhsInput = document.getElementById("new-rhs");
  const area = document.getElementById("grammar-input");

  const lhs = lhsInput.value.trim();
  const rhs = rhsInput.value.trim();
  if (!lhs || !rhs) return;

  const lines = area.value.split("\n").map(l => l.trim()).filter(Boolean);
  let merged = false;

  for (let i = 0; i < lines.length; i++) {
    const parts = lines[i].split("->");
    if (parts.length === 2 && parts[0].trim() === lhs) {
      lines[i] = `${lhs} -> ${parts[1].trim()} | ${rhs}`;
      merged = true;
      break;
    }
  }

  if (!merged) {
    lines.push(`${lhs} -> ${rhs}`);
  }

  area.value = lines.join("\n");
  lhsInput.value = "";
  rhsInput.value = "";
  updateFormalTupleDisplay();
});

// Auto-Hunt Ambiguous Counterexample
function autoHuntAmbiguity() {
  stopAutoPlay();
  const banner = document.getElementById("status-banner");
  try {
    const grammar = parseGrammar(document.getElementById("grammar-input").value);
    const queue = [[grammar.startSymbol]];
    const tested = new Set();
    let iterations = 0;

    while (queue.length > 0 && iterations < 450) {
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
            runAnalysis(false); // Start at Step 0 so user can step through the discovery
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

// Playback Button Wiring
document.getElementById("btn-first").addEventListener("click", () => {
  stopAutoPlay();
  currentAnalysis.currentStep = 0;
  renderCurrentStepView();
});

document.getElementById("btn-prev").addEventListener("click", () => {
  stopAutoPlay();
  if (currentAnalysis.currentStep > 0) {
    currentAnalysis.currentStep--;
    renderCurrentStepView();
  }
});

document.getElementById("btn-next").addEventListener("click", () => {
  stopAutoPlay();
  if (currentAnalysis.currentStep < currentAnalysis.maxSteps) {
    currentAnalysis.currentStep++;
    renderCurrentStepView();
  }
});

document.getElementById("btn-last").addEventListener("click", () => {
  stopAutoPlay();
  currentAnalysis.currentStep = currentAnalysis.maxSteps;
  renderCurrentStepView();
});

document.getElementById("btn-autoplay").addEventListener("click", () => {
  if (currentAnalysis.autoPlayTimer) {
    stopAutoPlay();
    return;
  }
  if (currentAnalysis.currentStep >= currentAnalysis.maxSteps) {
    currentAnalysis.currentStep = 0;
    renderCurrentStepView();
  }
  document.getElementById("btn-autoplay").textContent = "⏸ Pause";
  currentAnalysis.autoPlayTimer = setInterval(() => {
    if (currentAnalysis.currentStep < currentAnalysis.maxSteps) {
      currentAnalysis.currentStep++;
      renderCurrentStepView();
    } else {
      stopAutoPlay();
    }
  }, 1100);
});

// Preset & Input Wiring
document.querySelectorAll(".btn-preset").forEach(btn => {
  btn.addEventListener("click", () => {
    document.querySelectorAll(".btn-preset").forEach(b => b.classList.remove("active"));
    btn.classList.add("active");
    const preset = PRESETS[btn.dataset.preset];
    document.getElementById("grammar-input").value = preset.grammar;
    document.getElementById("string-input").value = preset.input;
    runAnalysis(false);
  });
});

document.getElementById("grammar-input").addEventListener("input", updateFormalTupleDisplay);
document.getElementById("parse-btn").addEventListener("click", () => runAnalysis(false));
document.getElementById("hunt-btn").addEventListener("click", autoHuntAmbiguity);

window.addEventListener("DOMContentLoaded", () => {
  document.getElementById("grammar-input").value = PRESETS["ambiguous-expr"].grammar;
  document.getElementById("string-input").value = PRESETS["ambiguous-expr"].input;
  runAnalysis(false);
});