import React, { useState, useEffect, useRef } from 'react';
import { 
  Menu, X, Upload, Table2, Sigma, Cpu, Play, Copy, Check, 
  Settings2, Layers, Binary, Code2, Zap, TerminalSquare, Grid, Sparkles, ChevronRight, Sliders, Loader2, Image as ImageIcon, AlertCircle
} from 'lucide-react';

// --- LOGIC ENGINE ---

const countOnes = (str: string) => (str.match(/1/g) || []).length;

const diffByOne = (str1: string, str2: string) => {
  let diffCount = 0;
  let diffIndex = -1;
  for (let i = 0; i < str1.length; i++) {
    if (str1[i] !== str2[i]) {
      diffCount++;
      diffIndex = i;
    }
  }
  return diffCount === 1 ? diffIndex : -1;
};

// Quine-McCluskey Minimization Algorithm
const minimizeBoolean = (numVars: number, minterms: number[], dontCares: number[]) => {
  if (minterms.length === 0) return '0';
  if (minterms.length + dontCares.length === Math.pow(2, numVars)) return '1';

  const pad = (num: number) => num.toString(2).padStart(numVars, '0');
  let terms = [...minterms, ...dontCares].map(m => ({
    val: pad(m),
    covered: false,
    mintermsCovered: [m]
  }));

  const uniqueTermsMap = new Map();
  terms.forEach(t => uniqueTermsMap.set(t.val, t));
  terms = Array.from(uniqueTermsMap.values());

  let primeImplicants: any[] = [];
  let currentGroup = terms;

  while (currentGroup.length > 0) {
    let nextGroup: any[] = [];
    let combinedSet = new Set<string>();
    
    for (let i = 0; i < currentGroup.length; i++) {
      for (let j = i + 1; j < currentGroup.length; j++) {
        const t1 = currentGroup[i];
        const t2 = currentGroup[j];
        const diffIdx = diffByOne(t1.val, t2.val);
        
        if (diffIdx !== -1) {
          t1.covered = true;
          t2.covered = true;
          const newVal = t1.val.substring(0, diffIdx) + '-' + t1.val.substring(diffIdx + 1);
          if (!combinedSet.has(newVal)) {
            combinedSet.add(newVal);
            nextGroup.push({
              val: newVal,
              covered: false,
              mintermsCovered: [...new Set([...t1.mintermsCovered, ...t2.mintermsCovered])]
            });
          }
        }
      }
    }
    
    currentGroup.forEach(t => {
      if (!t.covered) primeImplicants.push(t);
    });
    
    currentGroup = nextGroup;
  }

  let essentials: any[] = [];
  let remainingMinterms = new Set(minterms);

  const chart: Record<number, number[]> = {};
  minterms.forEach(m => chart[m] = []);
  primeImplicants.forEach((pi, piIdx) => {
    pi.mintermsCovered.forEach((m: number) => {
      if (chart[m]) chart[m].push(piIdx);
    });
  });

  for (let m in chart) {
    if (chart[m].length === 1 && remainingMinterms.has(parseInt(m))) {
      const piIdx = chart[m][0];
      const essentialPI = primeImplicants[piIdx];
      if (!essentials.includes(essentialPI)) {
        essentials.push(essentialPI);
        essentialPI.mintermsCovered.forEach((coveredM: number) => remainingMinterms.delete(coveredM));
      }
    }
  }

  while (remainingMinterms.size > 0) {
    let bestPI: any = null;
    let maxCovered = 0;
    
    primeImplicants.forEach(pi => {
      if (!essentials.includes(pi)) {
        let covers = pi.mintermsCovered.filter((m: number) => remainingMinterms.has(m)).length;
        if (covers > maxCovered) {
          maxCovered = covers;
          bestPI = pi;
        }
      }
    });

    if (bestPI) {
      essentials.push(bestPI);
      bestPI.mintermsCovered.forEach((m: number) => remainingMinterms.delete(m));
    } else {
      break;
    }
  }

  const varNames = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'];
  const expression = essentials.map(pi => {
    let termStr = '';
    for (let i = 0; i < pi.val.length; i++) {
      if (pi.val[i] === '1') termStr += varNames[i];
      if (pi.val[i] === '0') termStr += varNames[i] + "'";
    }
    return termStr || '1';
  }).join(' + ');

  return expression || '0';
};

const parseExpressionToTerms = (expr: string) => {
  if (expr === '0' || expr === '1') return [];
  const sumTerms = expr.split(' + ');
  return sumTerms.map(term => {
    const vars: { name: string; not: boolean }[] = [];
    for (let i = 0; i < term.length; i++) {
      if (term[i] >= 'A' && term[i] <= 'H') {
        let isNot = term[i+1] === "'";
        vars.push({ name: term[i], not: isNot });
        if (isNot) i++;
      }
    }
    return vars;
  });
};

// --- RTL GENERATORS ---
const generateVerilog = (numVars: number, expr: string) => {
  const vars = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'].slice(0, numVars);
  let vExpr = expr.replace(/\+/g, '|').replace(/([A-H])'/g, '~$1').replace(/([A-H])(?=[A-H~])/g, '$1 & ');
  let cleanExpr = vExpr.split(' | ').map(term => {
    let t = '';
    for(let i=0; i<term.length; i++) {
      t += term[i];
      if (term[i].match(/[A-H]/) && term[i+1] && term[i+1].match(/[A-H~]/)) {
        t += ' & ';
      }
    }
    return t;
  }).join(' | ');

  if (expr === '1') cleanExpr = "1'b1";
  if (expr === '0') cleanExpr = "1'b0";

  return `module logic_circuit(
    input wire ${vars.join(', ')},
    output wire Y
);

    // Auto-generated SOP implementation
    assign Y = ${cleanExpr};

endmodule`;
};

const generateVHDL = (numVars: number, expr: string) => {
  const vars = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'].slice(0, numVars);
  let vExpr = expr.replace(/\+/g, ' OR ').replace(/([A-H])'/g, 'NOT $1');
  
  let cleanExpr = vExpr.split(' OR ').map(term => {
     let parts: string[] = [];
     let current = '';
     for(let i=0; i<term.length; i++){
       if(term[i] === 'N') { current += 'NOT '; i+=3; }
       else if(term[i] !== ' ') {
         current += term[i];
         parts.push(current);
         current = '';
       }
     }
     return parts.join(' AND ');
  }).join(') OR (');
  
  if (cleanExpr.includes(' OR ')) cleanExpr = `(${cleanExpr})`;

  if (expr === '1') cleanExpr = "'1'";
  if (expr === '0') cleanExpr = "'0'";

  return `library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity logic_circuit is
    Port ( ${vars.map(v => `${v} : in STD_LOGIC`).join(';\n           ')};
           Y : out STD_LOGIC);
end logic_circuit;

architecture Behavioral of logic_circuit is
begin

    -- Auto-generated SOP implementation
    Y <= ${cleanExpr};

end Behavioral;`;
};

// --- GEMINI VISION API FOR ACCURATE IMAGE SCANNING ---
async function scanTruthTableWithGemini(base64Data: string, mimeType: string) {
  const apiKey = "";
  const delays = [1000, 2000, 4000, 8000, 16000];
  
  const promptText = `Analyze this image of a truth table, handwritten logic diagram, or boolean table. 
Extract:
1. 'numVars': Number of input variables (usually 2, 3, or 4, between 2 and 8).
2. 'outputs': An array of string output states ('0', '1', or 'X' for don't-care) corresponding to rows from minterm index 0 up to 2^numVars - 1. 
If any output row is ambiguous, infer standard logic or default to '0'. Ensure the length of the array is exactly 2^numVars.`;

  for (let attempt = 0; attempt < 5; attempt++) {
    try {
      const response = await fetch(
        `https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-flash-preview-09-2025:generateContent?key=${apiKey}`,
        {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            contents: [{
              role: 'user',
              parts: [
                { text: promptText },
                { inlineData: { mimeType, data: base64Data } }
              ]
            }],
            generationConfig: {
              responseMimeType: "application/json",
              responseSchema: {
                type: "OBJECT",
                properties: {
                  numVars: { type: "INTEGER" },
                  outputs: {
                    type: "ARRAY",
                    items: { type: "STRING" },
                    description: "Array of '0', '1', or 'X' values for each truth table row in binary order."
                  }
                },
                required: ["numVars", "outputs"]
              }
            }
          })
        }
      );

      if (!response.ok) {
        throw new Error(`API Error: ${response.statusText}`);
      }

      const result = await response.json();
      const rawText = result.candidates?.[0]?.content?.parts?.[0]?.text;
      if (!rawText) throw new Error("No analysis result returned.");

      const parsed = JSON.parse(rawText);
      return parsed as { numVars: number; outputs: string[] };
    } catch (err) {
      if (attempt === 4) throw err;
      await new Promise(res => setTimeout(res, delays[attempt]));
    }
  }
  throw new Error("Failed to scan image after multiple retries.");
}

const TerminalWindow = ({ code, language }: { code: string; language: string }) => {
  const [copied, setCopied] = useState(false);

  const handleCopy = () => {
    navigator.clipboard.writeText(code);
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  };

  return (
    <div className="relative rounded-2xl overflow-hidden bg-[#070B12] border border-amber-500/20 shadow-[0_10px_30px_rgba(0,0,0,0.5)] transition-all hover:border-amber-500/40">
      <div className="flex items-center justify-between px-5 py-3 bg-[#0E1422] border-b border-amber-500/10">
        <div className="flex items-center space-x-2">
          <div className="w-3 h-3 rounded-full bg-amber-500/60 border border-amber-400/40"></div>
          <div className="w-3 h-3 rounded-full bg-emerald-500/60 border border-emerald-400/40"></div>
          <div className="w-3 h-3 rounded-full bg-cyan-500/60 border border-cyan-400/40"></div>
          <span className="ml-3 text-[11px] font-mono tracking-widest uppercase text-amber-200/60 font-semibold">Synthesized RTL Source</span>
        </div>
        <div className="flex items-center gap-3">
          <span className="text-xs font-mono font-semibold px-2.5 py-0.5 rounded-full bg-amber-400/10 text-amber-300 border border-amber-400/20">{language.toUpperCase()}</span>
          <button 
            onClick={handleCopy} 
            className="flex items-center gap-1.5 text-xs text-slate-300 hover:text-amber-300 bg-white/5 hover:bg-amber-500/10 px-3 py-1.5 rounded-lg border border-white/10 hover:border-amber-500/30 transition-all font-mono"
          >
            {copied ? (
              <>
                <Check size={14} className="text-emerald-400" />
                <span className="text-emerald-400">COPIED</span>
              </>
            ) : (
              <>
                <Copy size={14} />
                <span>COPY CODE</span>
              </>
            )}
          </button>
        </div>
      </div>
      <div className="p-5 overflow-x-auto">
        <pre className="text-xs font-mono leading-relaxed text-slate-200 tracking-wide">
          <code dangerouslySetInnerHTML={{
            __html: code
              .replace(/(module|input|output|wire|assign|endmodule|library|use|entity|is|Port|out|in|architecture|of|begin|end|STD_LOGIC|STD_LOGIC_1164|ALL)/g, '<span class="text-[#F472B6] font-semibold">$1</span>')
              .replace(/(&#x27;|'|\||&amp;|&|~|NOT|AND|OR)/gi, '<span class="text-[#38BDF8] font-bold">$1</span>')
              .replace(/(\/\/.*|--.*)/g, '<span class="text-[#10B981] font-medium opacity-80">$1</span>')
          }} />
        </pre>
      </div>
    </div>
  );
};

const KMapRenderer = ({ numVars, truthTable }: { numVars: number; truthTable: any[] }) => {
  if (numVars > 4) {
    return (
      <div className="p-5 bg-[#090D16] rounded-xl border border-amber-500/15 text-amber-200/80 text-xs font-mono text-center tracking-wide">
        ✨ Visual K-Map matrix active for N ≤ 4. Tabular Quine-McCluskey minimization matrix active for N = {numVars} ({Math.pow(2, numVars)} minterms).
      </div>
    );
  }

  const getVal = (idx: number) => truthTable[idx] ? truthTable[idx].output : '0';

  const gray2 = [{ label: '0', val: 0 }, { label: '1', val: 1 }];
  const gray4 = [
    { label: '00', val: 0 },
    { label: '01', val: 1 },
    { label: '11', val: 3 },
    { label: '10', val: 2 }
  ];

  let rowHeaders: any[] = [], colHeaders: any[] = [];
  let rowVarLabel = '', colVarLabel = '';
  let getCellIndex = (r: number, c: number) => 0;

  if (numVars === 2) {
    rowVarLabel = 'A';
    colVarLabel = 'B';
    rowHeaders = gray2;
    colHeaders = gray2;
    getCellIndex = (r, c) => (r << 1) | c;
  } else if (numVars === 3) {
    rowVarLabel = 'A';
    colVarLabel = 'BC';
    rowHeaders = gray2;
    colHeaders = gray4;
    getCellIndex = (r, c) => (r << 2) | c;
  } else if (numVars === 4) {
    rowVarLabel = 'AB';
    colVarLabel = 'CD';
    rowHeaders = gray4;
    colHeaders = gray4;
    getCellIndex = (r, c) => (r << 2) | c;
  }

  return (
    <div className="w-full overflow-x-auto bg-[#070A11] p-6 rounded-2xl border border-white/10 flex flex-col items-center shadow-2xl relative">
      <div className="text-xs font-mono text-amber-200/70 mb-4 flex items-center gap-2 tracking-widest uppercase font-semibold">
        <span className="w-2 h-2 rounded-full bg-amber-400 shadow-[0_0_8px_#F59E0B]"></span>
        Karnaugh Map Matrix ({numVars} Variables)
      </div>

      <div className="inline-block border border-amber-500/20 rounded-xl overflow-hidden bg-[#0D121F] shadow-xl">
        <table className="border-collapse font-mono text-xs">
          <thead>
            <tr>
              <th className="p-3.5 bg-[#121828] border-b border-r border-amber-500/20 text-slate-400 text-xs text-center font-bold tracking-wider">
                {rowVarLabel} \ {colVarLabel}
              </th>
              {colHeaders.map((col, idx) => (
                <th key={idx} className="p-3.5 bg-[#121828] border-b border-r border-amber-500/20 text-amber-300 text-center w-16 font-semibold tracking-wider">
                  {col.label}
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {rowHeaders.map((row, rIdx) => (
              <tr key={rIdx}>
                <td className="p-3.5 bg-[#121828] border-b border-r border-amber-500/20 text-cyan-300 font-bold text-center">
                  {row.label}
                </td>
                {colHeaders.map((col, cIdx) => {
                  const mIdx = getCellIndex(row.val, col.val);
                  const val = getVal(mIdx);
                  return (
                    <td 
                      key={cIdx} 
                      className={`p-3.5 border-b border-r border-amber-500/10 text-center font-bold text-base transition-all duration-300 ${
                        val === '1' ? 'bg-emerald-500/20 text-emerald-300 border-emerald-500/30 shadow-[inset_0_0_12px_rgba(16,185,129,0.2)]' :
                        val === 'X' ? 'bg-amber-500/20 text-amber-300 border-amber-500/30 shadow-[inset_0_0_12px_rgba(245,158,11,0.2)]' :
                        'text-slate-600 hover:text-slate-400'
                      }`}
                    >
                      <div className="relative group flex flex-col items-center justify-center">
                        <span className="tracking-widest">{val}</span>
                        <span className="text-[9px] text-slate-500 font-mono font-normal opacity-70">m{mIdx}</span>
                      </div>
                    </td>
                  );
                })}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
};

const CircuitRenderer = ({ expression, mode }: { expression: string; mode: string }) => {
  if (expression === '0' || expression === '1') {
    return (
      <div className="p-8 text-center text-slate-400 font-mono bg-[#070A11] rounded-2xl border border-white/10">
        Constant output <span className="text-amber-300 font-bold">Y = {expression}</span>. Logic gate network idle.
      </div>
    );
  }

  const terms = parseExpressionToTerms(expression);
  if (terms.length === 0) return null;

  const uniqueVarsSet = new Set<string>();
  terms.forEach(t => t.forEach(v => uniqueVarsSet.add(v.name)));
  const sortedVars = Array.from(uniqueVarsSet).sort();

  const modeColor = mode === 'NAND' ? '#38BDF8' : mode === 'NOR' ? '#E879F9' : '#34D399';
  const wireColor = mode === 'NAND' ? '#38BDF8' : mode === 'NOR' ? '#E879F9' : '#38BDF8';

  const neededInverters = new Set<string>();
  terms.forEach(term => {
    term.forEach(v => {
      if (mode === 'NOR') {
        if (term.length > 1 && !v.not) neededInverters.add(v.name);
        if (term.length === 1 && v.not) neededInverters.add(v.name);
      } else {
        if (v.not) neededInverters.add(v.name);
      }
    });
  });

  const invVarsList = Array.from(neededInverters).sort();

  const totalRows = Math.max(sortedVars.length, terms.length);
  const svgHeight = Math.max(340, totalRows * 65 + 70);
  const svgWidth = 860;

  const inputX = 50;
  const inverterX = 180;
  const stage1X = 420;
  const stage2X = 680;
  const outputX = 820;

  const varYPositions: Record<string, number> = {};
  sortedVars.forEach((v, i) => {
    varYPositions[v] = 60 + i * (svgHeight - 120) / Math.max(1, sortedVars.length - 1);
  });

  const invYPositions: Record<string, number> = {};
  invVarsList.forEach((v) => {
    invYPositions[v] = varYPositions[v] + 20;
  });

  const signalSources: Record<string, { x: number; y: number }> = {};
  sortedVars.forEach(v => {
    signalSources[v] = { x: inputX + 20, y: varYPositions[v] };
  });

  invVarsList.forEach(v => {
    signalSources[`${v}'`] = { x: inverterX + 54, y: invYPositions[v] };
  });

  const termYPositions = terms.map((_, idx) => 60 + idx * (svgHeight - 120) / Math.max(1, terms.length - 1));

  const renderGateSymbol = (type: string, x: number, y: number, label: string, width = 48, height = 32) => {
    const halfH = height / 2;
    const gateStroke = mode === 'NAND' ? '#38BDF8' : mode === 'NOR' ? '#E879F9' : (type === 'OR' ? '#E879F9' : type === 'NOT' ? '#34D399' : '#38BDF8');
    const gateFill = `${gateStroke}22`;

    return (
      <g transform={`translate(${x}, ${y - halfH})`}>
        <line x1="-10" y1={halfH - 6} x2="0" y2={halfH - 6} stroke={gateStroke} strokeWidth="2" />
        <line x1="-10" y1={halfH + 6} x2="0" y2={halfH + 6} stroke={gateStroke} strokeWidth="2" />
        
        {type === 'NOT' ? (
          <g>
            <polygon points={`0,2 ${width * 0.7},${halfH} 0,${height - 2}`} fill={gateFill} stroke={gateStroke} strokeWidth="2" />
            <circle cx={width * 0.7 + 4} cy={halfH} r="3.5" fill="#0D121F" stroke={gateStroke} strokeWidth="2" />
          </g>
        ) : (type === 'AND' || type === 'NAND') ? (
          <g>
            <path d={`M 0 0 L ${width * 0.5} 0 A ${halfH} ${halfH} 0 0 1 ${width * 0.5} ${height} L 0 ${height} Z`} fill={gateFill} stroke={gateStroke} strokeWidth="2" />
            {type === 'NAND' && <circle cx={width + 4} cy={halfH} r="3.5" fill="#0D121F" stroke={gateStroke} strokeWidth="2" />}
          </g>
        ) : (
          <g>
            <path d={`M 0 0 Q ${width * 0.3} ${halfH} 0 ${height} Q ${width * 0.75} ${height} ${width} ${halfH} Q ${width * 0.75} 0 0 0 Z`} fill={gateFill} stroke={gateStroke} strokeWidth="2" />
            {type === 'NOR' && <circle cx={width + 4} cy={halfH} r="3.5" fill="#0D121F" stroke={gateStroke} strokeWidth="2" />}
          </g>
        )}
        <text x={width / 3} y={halfH + 4} fill="#FFFFFF" fontSize="9" fontFamily="monospace" fontWeight="bold">{label}</text>
      </g>
    );
  };

  let currentConnIndex = 0;

  return (
    <div className="w-full flex flex-col gap-4">
      <div className="flex items-center justify-between px-5 py-2.5 bg-[#070A11] rounded-xl border border-white/10 text-xs font-mono">
        <span className="text-slate-400 tracking-wider">Circuit Architecture:</span>
        <span className="font-semibold text-amber-300 bg-amber-400/10 px-3 py-1 rounded-full border border-amber-400/20">
          Strict 2-Input Configuration ({mode} Standard)
        </span>
      </div>

      <div className="w-full overflow-x-auto bg-[#070A11] p-5 rounded-2xl border border-white/10 shadow-2xl">
        <svg width={svgWidth} height={svgHeight} className="min-w-max mx-auto">
          <defs>
            <pattern id="grid" width="20" height="20" patternUnits="userSpaceOnUse">
              <path d="M 20 0 L 0 0 0 20" fill="none" stroke="rgba(255, 255, 255, 0.03)" strokeWidth="1" />
            </pattern>
          </defs>
          <rect width="100%" height="100%" fill="url(#grid)" />

          {sortedVars.map(v => {
            const mainY = varYPositions[v];
            const invY = invYPositions[v];
            const hasInverter = neededInverters.has(v);

            return (
              <g key={v}>
                <text x={inputX - 25} y={mainY + 4} fill="#F1F5F9" className="font-mono text-sm font-bold">{v}</text>
                <circle cx={inputX} cy={mainY} r="3.5" fill="#38BDF8" />
                <line x1={inputX} y1={mainY} x2={stage1X - 100} y2={mainY} stroke={wireColor} strokeWidth="2" />

                {hasInverter && (
                  <g>
                    <circle cx={inverterX - 30} cy={mainY} r="3" fill={wireColor} />
                    <path 
                      d={`M ${inverterX - 30} ${mainY} L ${inverterX - 15} ${mainY} L ${inverterX - 15} ${invY} L ${inverterX} ${invY}`} 
                      fill="none" 
                      stroke={wireColor} 
                      strokeWidth="2" 
                    />
                    <line x1={inverterX - 10} y1={invY} x2={inverterX} y2={invY - 6} stroke={wireColor} strokeWidth="2" />
                    <line x1={inverterX - 10} y1={invY} x2={inverterX} y2={invY + 6} stroke={wireColor} strokeWidth="2" />
                    {renderGateSymbol(
                      mode === 'NAND' ? 'NAND' : mode === 'NOR' ? 'NOR' : 'NOT',
                      inverterX,
                      invY,
                      mode === 'NAND' ? 'NAND' : mode === 'NOR' ? 'NOR' : 'NOT'
                    )}
                    <line x1={inverterX + 54} y1={invY} x2={stage1X - 100} y2={invY} stroke={wireColor} strokeWidth="2" />
                    <text x={inverterX + 60} y={invY - 5} fill="#94A3B8" className="font-mono text-[10px]">{v}'</text>
                  </g>
                )}
              </g>
            );
          })}

          {terms.map((term, termIdx) => {
            const termY = termYPositions[termIdx];
            const gateType = mode === 'NAND' ? 'NAND' : mode === 'NOR' ? 'NOR' : 'AND';

            if (term.length === 1) {
              const v = term[0];
              const sigKey = mode === 'NOR' ? (v.not ? `${v.name}'` : v.name) : (v.not ? `${v.name}'` : v.name);
              const src = signalSources[sigKey] || { x: inputX + 20, y: varYPositions[v.name] };

              if (mode === 'NAND') {
                const connIndex = currentConnIndex++;
                const channelX = stage1X - 30 - (connIndex * 12);

                return (
                  <g key={termIdx}>
                    <circle cx={src.x} cy={src.y} r="2.5" fill={wireColor} />
                    <path 
                      d={`M ${src.x} ${src.y} L ${channelX} ${src.y} L ${channelX} ${termY} L ${stage1X} ${termY}`}
                      fill="none" 
                      stroke={wireColor} 
                      strokeWidth="2" 
                    />
                    <line x1={stage1X - 10} y1={termY} x2={stage1X} y2={termY - 6} stroke={wireColor} strokeWidth="2" />
                    <line x1={stage1X - 10} y1={termY} x2={stage1X} y2={termY + 6} stroke={wireColor} strokeWidth="2" />
                    {renderGateSymbol('NAND', stage1X, termY, 'NAND')}
                  </g>
                );
              }
              return null;
            }

            return (
              <g key={termIdx}>
                {term.map((v, vIdx) => {
                  let sigKey = mode === 'NOR' ? (!v.not ? `${v.name}'` : v.name) : (v.not ? `${v.name}'` : v.name);
                  const src = signalSources[sigKey] || { x: inputX + 20, y: varYPositions[v.name] };
                  const inputOffset = vIdx === 0 ? -6 : 6;
                  
                  const connIndex = currentConnIndex++;
                  const channelX = stage1X - 25 - (connIndex * 12);

                  return (
                    <g key={vIdx}>
                      <circle cx={src.x} cy={src.y} r="2.5" fill={wireColor} />
                      <path 
                        d={`M ${src.x} ${src.y} L ${channelX} ${src.y} L ${channelX} ${termY + inputOffset} L ${stage1X} ${termY + inputOffset}`} 
                        fill="none" 
                        stroke={wireColor} 
                        strokeWidth="2" 
                      />
                    </g>
                  );
                })}

                {renderGateSymbol(gateType, stage1X, termY, gateType)}
              </g>
            );
          })}

          {(() => {
            const outputY = svgHeight / 2;

            if (terms.length === 1) {
              const term = terms[0];
              let startX = stage1X + 54;
              let startY = termYPositions[0];

              if (term.length === 1) {
                const v = term[0];
                const sigKey = mode === 'NOR' ? (v.not ? `${v.name}'` : v.name) : (v.not ? `${v.name}'` : v.name);
                const src = signalSources[sigKey] || { x: inputX + 20, y: varYPositions[v.name] };
                startX = src.x;
                startY = src.y;
              }

              if (mode === 'NAND' && term.length > 1) {
                return (
                  <g>
                    <line x1={startX} y1={startY} x2={stage2X - 10} y2={startY} stroke={wireColor} strokeWidth="2" />
                    <line x1={stage2X - 10} y1={startY} x2={stage2X} y2={startY - 6} stroke={wireColor} strokeWidth="2" />
                    <line x1={stage2X - 10} y1={startY} x2={stage2X} y2={startY + 6} stroke={wireColor} strokeWidth="2" />
                    {renderGateSymbol('NAND', stage2X, startY, 'NAND')}
                    <line x1={stage2X + 54} y1={startY} x2={outputX} y2={startY} stroke="#FFFFFF" strokeWidth="2.5" />
                    <text x={outputX + 10} y={startY + 5} fill="#FFFFFF" className="font-mono text-lg font-bold">Y</text>
                  </g>
                );
              }

              return (
                <g>
                  <line x1={startX} y1={startY} x2={outputX} y2={startY} stroke="#FFFFFF" strokeWidth="2.5" />
                  <text x={outputX + 10} y={startY + 5} fill="#FFFFFF" className="font-mono text-lg font-bold">Y</text>
                </g>
              );
            }

            const stage2Type = mode === 'NAND' ? 'NAND' : mode === 'NOR' ? 'NOR' : 'OR';

            return (
              <g>
                {terms.map((term, termIdx) => {
                  const termY = termYPositions[termIdx];
                  let srcX = stage1X + 54;
                  let srcY = termY;

                  if (term.length === 1 && mode !== 'NAND') {
                    const v = term[0];
                    const sigKey = mode === 'NOR' ? (v.not ? `${v.name}'` : v.name) : (v.not ? `${v.name}'` : v.name);
                    const src = signalSources[sigKey] || { x: inputX + 20, y: varYPositions[v.name] };
                    srcX = src.x;
                    srcY = src.y;
                  }

                  const inputOffset = (termIdx - (terms.length - 1) / 2) * 12;
                  const stage2ChannelX = stage2X - 35 - (termIdx * 14);

                  return (
                    <g key={termIdx}>
                      <circle cx={srcX} cy={srcY} r="2.5" fill={modeColor} />
                      <path 
                        d={`M ${srcX} ${srcY} L ${stage2ChannelX} ${srcY} L ${stage2ChannelX} ${outputY + inputOffset} L ${stage2X} ${outputY + inputOffset}`} 
                        fill="none" 
                        stroke={modeColor} 
                        strokeWidth="2" 
                      />
                    </g>
                  );
                })}

                {renderGateSymbol(stage2Type, stage2X, outputY, stage2Type)}

                {mode === 'NOR' ? (
                  <g>
                    <line x1={stage2X + 54} y1={outputY} x2={stage2X + 100} y2={outputY} stroke={modeColor} strokeWidth="2" />
                    <line x1={stage2X + 100} y1={outputY} x2={stage2X + 110} y2={outputY - 6} stroke={modeColor} strokeWidth="2" />
                    <line x1={stage2X + 100} y1={outputY} x2={stage2X + 110} y2={outputY + 6} stroke={modeColor} strokeWidth="2" />
                    {renderGateSymbol('NOR', stage2X + 110, outputY, 'NOR')}
                    <line x1={stage2X + 164} y1={outputY} x2={outputX} y2={outputY} stroke="#FFFFFF" strokeWidth="2.5" />
                    <text x={outputX + 10} y={outputY + 5} fill="#FFFFFF" className="font-mono text-lg font-bold">Y</text>
                  </g>
                ) : (
                  <g>
                    <line x1={stage2X + 54} y1={outputY} x2={outputX} y2={outputY} stroke="#FFFFFF" strokeWidth="2.5" />
                    <text x={outputX + 10} y={outputY + 5} fill="#FFFFFF" className="font-mono text-lg font-bold">Y</text>
                  </g>
                )}
              </g>
            );
          })()}
        </svg>
      </div>
    </div>
  );
};

export default function App() {
  const [activeModule, setActiveModule] = useState('truthTable');
  const [numVars, setNumVars] = useState(3);
  
  const [truthTable, setTruthTable] = useState<{ inputs: number[]; output: string; index: number }[]>([]);
  const [mintermsStr, setMintermsStr] = useState('0, 2, 4, 6');
  const [dontCaresStr, setDontCaresStr] = useState('');

  const [circuitMode, setCircuitMode] = useState('Basic');
  const [codeLang, setCodeLang] = useState('Verilog');

  const [minimizedExpr, setMinimizedExpr] = useState('');
  
  // OCR & Image Upload States
  const fileInputRef = useRef<HTMLInputElement>(null);
  const [isScanning, setIsScanning] = useState(false);
  const [scanError, setScanError] = useState<string | null>(null);

  useEffect(() => {
    const numRows = Math.pow(2, numVars);
    const newTable = [];
    for (let i = 0; i < numRows; i++) {
      const inputs = i.toString(2).padStart(numVars, '0').split('').map(Number);
      newTable.push({ inputs, output: '0', index: i });
    }
    setTruthTable(newTable);
  }, [numVars]);

  useEffect(() => {
    let minterms: number[] = [];
    let dontCares: number[] = [];

    if (activeModule === 'truthTable') {
      truthTable.forEach((row, idx) => {
        if (row.output === '1') minterms.push(idx);
        if (row.output === 'X') dontCares.push(idx);
      });
    } else {
      const parseList = (str: string) => str.split(',').map(s => parseInt(s.trim())).filter(n => !isNaN(n) && n < Math.pow(2, numVars));
      minterms = parseList(mintermsStr);
      dontCares = parseList(dontCaresStr);
    }

    const result = minimizeBoolean(numVars, minterms, dontCares);
    setMinimizedExpr(result);
  }, [truthTable, mintermsStr, dontCaresStr, numVars, activeModule]);

  const toggleOutput = (index: number) => {
    const newTable = [...truthTable];
    const current = newTable[index].output;
    newTable[index].output = current === '0' ? '1' : current === '1' ? 'X' : '0';
    setTruthTable(newTable);
  };

  // --- HANDLER FOR SCANNING IMAGE VIA GEMINI API ---
  const handleImageScan = async (e: React.ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0];
    if (!file) return;

    setIsScanning(true);
    setScanError(null);

    try {
      // Convert image to base64
      const reader = new FileReader();
      const base64Promise = new Promise<string>((resolve, reject) => {
        reader.onload = () => {
          const resultStr = reader.result as string;
          const base64 = resultStr.split(',')[1];
          resolve(base64);
        };
        reader.onerror = error => reject(error);
      });
      reader.readAsDataURL(file);

      const base64Data = await base64Promise;
      const parsedData = await scanTruthTableWithGemini(base64Data, file.type || 'image/png');

      const targetVars = Math.min(Math.max(parsedData.numVars || 3, 2), 8);
      const totalRows = Math.pow(2, targetVars);

      setNumVars(targetVars);

      const updatedTable = [];
      for (let i = 0; i < totalRows; i++) {
        const inputs = i.toString(2).padStart(targetVars, '0').split('').map(Number);
        let outVal = parsedData.outputs[i] || '0';
        outVal = ['0', '1', 'X', 'x'].includes(outVal) ? outVal.toUpperCase() : '0';
        updatedTable.push({ inputs, output: outVal, index: i });
      }

      setTruthTable(updatedTable);
    } catch (err: any) {
      console.error('Image scan error:', err);
      setScanError(err.message || 'Failed to analyze image. Please try a clearer photo.');
    } finally {
      setIsScanning(false);
      if (fileInputRef.current) fileInputRef.current.value = '';
    }
  };

  return (
    <div className="flex h-screen bg-[#070A11] text-slate-200 font-sans overflow-hidden antialiased relative">
      
      {/* Hidden Native File Input */}
      <input 
        type="file" 
        ref={fileInputRef} 
        accept="image/*" 
        className="hidden" 
        onChange={handleImageScan} 
      />

      {/* Subtle Ambient Studio Glows */}
      <div className="absolute top-0 left-0 w-96 h-96 bg-amber-500/5 rounded-full blur-[120px] pointer-events-none"></div>
      <div className="absolute bottom-0 right-0 w-96 h-96 bg-cyan-500/5 rounded-full blur-[120px] pointer-events-none"></div>

      {/* Primary Sidebar */}
      <div className="w-72 bg-[#0B0F19]/90 backdrop-blur-2xl border-r border-amber-500/10 flex flex-col z-20 shadow-2xl">
        <div className="p-6 flex items-center gap-3.5 border-b border-amber-500/10">
          <div className="p-2.5 rounded-xl bg-gradient-to-br from-amber-400/20 to-amber-600/10 border border-amber-400/30 shadow-[0_0_20px_rgba(245,158,11,0.2)]">
            <Zap className="text-amber-300 w-6 h-6" />
          </div>
          <div>
            <h1 className="text-lg font-black tracking-widest bg-clip-text text-transparent bg-gradient-to-r from-amber-200 via-amber-400 to-amber-100 font-mono">
              LOGIC STUDIO
            </h1>
            <p className="text-[10px] font-mono tracking-widest text-amber-200/50 font-semibold uppercase">Hardware CAD Suite</p>
          </div>
        </div>

        <nav className="flex-1 px-4 space-y-2.5 py-6">
          <div className="text-[10px] font-bold text-amber-200/50 uppercase tracking-widest mb-3 px-2 font-mono">
            Input Solvers
          </div>
          
          <button 
            onClick={() => setActiveModule('truthTable')}
            className={`w-full flex items-center justify-between px-4 py-3.5 rounded-xl transition-all duration-300 font-medium text-xs tracking-wider ${
              activeModule === 'truthTable' 
                ? 'bg-gradient-to-r from-amber-500/20 via-amber-500/10 to-transparent text-amber-300 border border-amber-400/40 shadow-[0_0_20px_rgba(245,158,11,0.15)] font-semibold' 
                : 'hover:bg-white/5 text-slate-400 hover:text-slate-200 border border-transparent'
            }`}
          >
            <div className="flex items-center gap-3">
              <Table2 size={18} className={activeModule === 'truthTable' ? 'text-amber-300' : 'text-slate-500'} />
              <span>Truth Table Solver</span>
            </div>
            <ChevronRight size={14} className={activeModule === 'truthTable' ? 'text-amber-300 opacity-100' : 'opacity-0'} />
          </button>

          <button 
            onClick={() => setActiveModule('canonical')}
            className={`w-full flex items-center justify-between px-4 py-3.5 rounded-xl transition-all duration-300 font-medium text-xs tracking-wider ${
              activeModule === 'canonical' 
                ? 'bg-gradient-to-r from-cyan-500/20 via-cyan-500/10 to-transparent text-cyan-300 border border-cyan-400/40 shadow-[0_0_20px_rgba(6,182,212,0.15)] font-semibold' 
                : 'hover:bg-white/5 text-slate-400 hover:text-slate-200 border border-transparent'
            }`}
          >
            <div className="flex items-center gap-3">
              <Sigma size={18} className={activeModule === 'canonical' ? 'text-cyan-300' : 'text-slate-500'} />
              <span>Canonical (Σ / Π)</span>
            </div>
            <ChevronRight size={14} className={activeModule === 'canonical' ? 'text-cyan-300 opacity-100' : 'opacity-0'} />
          </button>

          <div className="mt-8 mb-4 border-t border-amber-500/10 pt-6">
            <div className="text-[10px] font-bold text-amber-200/50 uppercase tracking-widest mb-4 px-2 font-mono flex items-center gap-2">
              <Sliders size={12} /> Signal Configuration
            </div>
            
            <div className="px-2 bg-white/[0.02] p-4 rounded-xl border border-white/5">
              <div className="flex justify-between items-center mb-3">
                <label className="text-xs font-mono font-medium text-slate-300">Variables (N)</label>
                <span className="px-2.5 py-0.5 rounded-full bg-amber-400/20 text-amber-300 font-mono text-xs font-bold border border-amber-400/30">
                  {numVars}
                </span>
              </div>
              <input 
                type="range" 
                min="2" max="8" 
                value={numVars} 
                onChange={(e) => setNumVars(parseInt(e.target.value))}
                className="w-full accent-amber-400 h-1.5 bg-slate-800 rounded-lg appearance-none cursor-pointer"
              />
              <div className="flex justify-between text-[10px] font-mono text-slate-500 mt-2.5">
                <span>2 (4 rows)</span>
                <span>8 (256 rows)</span>
              </div>
            </div>
          </div>
        </nav>
      </div>

      {/* Main Content Area */}
      <div className="flex-1 flex flex-col relative overflow-hidden">
        
        {/* Top Header/Toolbar */}
        <header className="h-16 border-b border-amber-500/10 flex items-center justify-between px-8 bg-[#0B0F19]/80 backdrop-blur-xl z-10 shadow-lg">
          <div className="flex items-center gap-3">
            <div className="w-2 h-2 rounded-full bg-emerald-400 shadow-[0_0_8px_#10B981]"></div>
            <span className="font-semibold text-slate-200 text-xs tracking-wider font-mono">
              {activeModule === 'truthTable' ? 'TRUTH TABLE MINIMIZER & SCHEMATIC SYNTHESIZER' : 'CANONICAL ∑ MINTERMS & ∏ MAXTERMS CONVERTER'}
            </span>
          </div>

          <div className="flex items-center gap-3">
            <span className="text-xs font-mono text-slate-400 uppercase tracking-widest">Gate Standard:</span>
            <div className="flex items-center gap-1 bg-[#060911] rounded-xl p-1 border border-white/10 shadow-inner">
              {[
                { id: 'Basic', label: '1. Standard Basic' },
                { id: 'NAND', label: '2. Only NAND' },
                { id: 'NOR', label: '3. Only NOR' }
              ].map(m => (
                <button
                  key={m.id}
                  onClick={() => setCircuitMode(m.id)}
                  className={`px-3.5 py-1.5 text-xs font-mono rounded-lg transition-all ${
                    circuitMode === m.id 
                      ? 'bg-gradient-to-r from-amber-500/20 to-amber-600/20 text-amber-300 border border-amber-400/40 shadow-sm font-semibold' 
                      : 'text-slate-400 hover:text-slate-200'
                  }`}
                >
                  {m.label}
                </button>
              ))}
            </div>
          </div>
        </header>

        {/* Workspace Splitter */}
        <div className="flex-1 flex overflow-hidden">
          
          {/* Input Panel (Left) */}
          <div className="w-[38%] min-w-[340px] border-r border-amber-500/10 flex flex-col bg-[#070A11] overflow-y-auto custom-scrollbar">
            <div className="p-6">
              
              {activeModule === 'truthTable' ? (
                <div className="space-y-6">
                  <div className="flex justify-between items-center">
                    <h2 className="text-xs font-mono font-semibold uppercase tracking-widest text-amber-200/70 flex items-center gap-2">
                      <Sparkles size={14} className="text-amber-400" /> Truth Table Output Grid
                    </h2>

                    {/* AI IMAGE SCAN BUTTON */}
                    <button 
                      onClick={() => fileInputRef.current?.click()}
                      disabled={isScanning}
                      className="flex items-center gap-2 text-xs bg-amber-500/10 hover:bg-amber-500/20 text-amber-300 border border-amber-500/30 px-3.5 py-1.5 rounded-lg transition-all font-mono font-medium disabled:opacity-50"
                    >
                      {isScanning ? (
                        <>
                          <Loader2 size={13} className="text-amber-400 animate-spin" />
                          <span>AI Scanning...</span>
                        </>
                      ) : (
                        <>
                          <Upload size={13} className="text-amber-400" />
                          <span>Scan Image</span>
                        </>
                      )}
                    </button>
                  </div>

                  {scanError && (
                    <div className="p-3 bg-rose-500/10 border border-rose-500/20 rounded-xl text-rose-300 text-xs font-mono flex items-center gap-2">
                      <AlertCircle size={14} className="shrink-0 text-rose-400" />
                      <span>{scanError}</span>
                    </div>
                  )}
                  
                  <div className="rounded-2xl border border-white/10 overflow-hidden bg-[#0D121F] shadow-2xl">
                    <div className="max-h-[62vh] overflow-y-auto custom-scrollbar">
                      {numVars > 6 && <div className="p-3 bg-amber-500/10 text-amber-300 text-xs text-center border-b border-amber-500/20 font-mono">Displaying first 256 rows for optimal performance.</div>}
                      <table className="w-full text-xs text-left">
                        <thead className="text-[11px] text-slate-400 uppercase bg-[#121828] sticky top-0 z-10 shadow-md font-mono">
                          <tr>
                            <th className="px-4 py-3.5 text-center">Row</th>
                            {Array.from({length: numVars}).map((_, i) => (
                              <th key={i} className="px-4 py-3.5 text-center font-mono text-cyan-300 font-bold">{String.fromCharCode(65 + i)}</th>
                            ))}
                            <th className="px-4 py-3.5 text-center border-l border-white/10 text-amber-400 font-bold">Y (Out)</th>
                          </tr>
                        </thead>
                        <tbody>
                          {truthTable.slice(0, 256).map((row, idx) => (
                            <tr key={idx} className="border-b border-white/5 hover:bg-white/5 transition-colors">
                              <td className="px-4 py-2 text-center text-slate-500 font-mono text-xs">{row.index}</td>
                              {row.inputs.map((val, vIdx) => (
                                <td key={vIdx} className="px-4 py-2 text-center font-mono text-slate-300 text-xs">{val}</td>
                              ))}
                              <td className="px-4 py-2 text-center border-l border-white/10">
                                <button 
                                  onClick={() => toggleOutput(idx)}
                                  className={`w-8 h-8 rounded-lg font-bold font-mono transition-all text-sm ${
                                    row.output === '1' ? 'bg-emerald-500/20 text-emerald-300 border border-emerald-400/50 shadow-[0_0_12px_rgba(16,185,129,0.25)]' :
                                    row.output === 'X' ? 'bg-amber-500/20 text-amber-300 border border-amber-400/50 shadow-[0_0_12px_rgba(245,158,11,0.25)]' :
                                    'bg-[#060911] text-slate-500 border border-white/10 hover:border-slate-400'
                                  }`}
                                >
                                  {row.output}
                                </button>
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </div>
              ) : (
                <div className="space-y-6">
                  <h2 className="text-xs font-mono font-semibold uppercase tracking-widest text-amber-200/70 flex items-center gap-2">
                    <Sparkles size={14} className="text-cyan-400" /> Canonical Input Configuration
                  </h2>
                  
                  <div className="space-y-6">
                    <label className="block bg-[#0D121F] p-5 rounded-2xl border border-white/10 shadow-2xl">
                      <span className="text-slate-200 text-xs font-semibold uppercase tracking-wider mb-2.5 flex items-center gap-2 font-mono">
                        <Sigma size={16} className="text-cyan-400" /> Minterms ($\Sigma m$)
                      </span>
                      <input 
                        type="text" 
                        value={mintermsStr}
                        onChange={(e) => setMintermsStr(e.target.value)}
                        placeholder="e.g. 0, 2, 4, 6"
                        className="w-full bg-[#060911] border border-white/10 rounded-xl px-4 py-3 text-white focus:outline-none focus:border-cyan-400 focus:ring-1 focus:ring-cyan-400/50 font-mono text-sm transition-all"
                      />
                      <p className="text-[11px] text-slate-500 mt-2 font-mono">Comma-separated minterm indices (0 to {Math.pow(2, numVars) - 1})</p>
                    </label>

                    <label className="block bg-[#0D121F] p-5 rounded-2xl border border-white/10 shadow-2xl">
                      <span className="text-slate-200 text-xs font-semibold uppercase tracking-wider mb-2.5 flex items-center gap-2 font-mono">
                        <span className="text-amber-400 font-bold font-mono">d</span> Don't Cares
                      </span>
                      <input 
                        type="text" 
                        value={dontCaresStr}
                        onChange={(e) => setDontCaresStr(e.target.value)}
                        placeholder="e.g. 1, 5"
                        className="w-full bg-[#060911] border border-white/10 rounded-xl px-4 py-3 text-white focus:outline-none focus:border-amber-400 focus:ring-1 focus:ring-amber-400/50 font-mono text-sm transition-all"
                      />
                      <p className="text-[11px] text-slate-500 mt-2 font-mono">Optional don't care conditions</p>
                    </label>
                  </div>
                </div>
              )}

            </div>
          </div>

          {/* Results Panel (Right) */}
          <div className="flex-1 flex flex-col bg-[#05080E] overflow-y-auto custom-scrollbar relative">
            
            <div className="p-8 space-y-8 z-10">
              
              {/* Boolean Equation Card */}
              <div className="bg-[#0D121F]/90 backdrop-blur-xl border border-amber-500/20 rounded-2xl p-6 shadow-2xl relative overflow-hidden transition-all hover:border-amber-500/40">
                <div className="absolute top-0 left-0 w-1.5 h-full bg-gradient-to-b from-amber-400 via-amber-500 to-cyan-500"></div>
                <h3 className="text-xs font-mono font-semibold text-amber-200/70 uppercase tracking-widest mb-4 flex items-center gap-2">
                  <Binary size={16} className="text-amber-400" /> Minimized Boolean Expression (Sum of Products)
                </h3>
                <div className="text-2xl font-mono text-white tracking-wider break-all flex flex-wrap items-center gap-2.5">
                  <span className="text-amber-400 font-bold">Y =</span> 
                  {minimizedExpr.split(' + ').map((term, i, arr) => (
                    <React.Fragment key={i}>
                      <span className="text-cyan-300 bg-cyan-500/10 px-3 py-1 rounded-xl border border-cyan-400/30 shadow-[0_0_15px_rgba(6,182,212,0.1)]">{term}</span>
                      {i < arr.length - 1 && <span className="text-slate-500 font-bold">+</span>}
                    </React.Fragment>
                  ))}
                </div>
              </div>

              {/* Karnaugh Map Display Card */}
              <div className="bg-[#0D121F]/90 backdrop-blur-xl border border-white/10 rounded-2xl p-6 shadow-2xl">
                 <h3 className="text-xs font-mono font-semibold text-amber-200/70 uppercase tracking-widest mb-4 flex items-center gap-2">
                   <Grid size={16} className="text-emerald-400" /> Karnaugh Map Diagram
                 </h3>
                 <KMapRenderer numVars={numVars} truthTable={truthTable} />
              </div>

              {/* Logic Gate Circuit Diagram Card */}
              <div className="bg-[#0D121F]/90 backdrop-blur-xl border border-white/10 rounded-2xl p-6 shadow-2xl">
                 <div className="flex justify-between items-center mb-6">
                    <h3 className="text-xs font-mono font-semibold text-amber-200/70 uppercase tracking-widest flex items-center gap-2">
                      <Cpu size={16} className="text-cyan-400" /> Logic Circuit Schematic
                    </h3>
                    <span className="text-xs bg-white/5 text-slate-300 px-3 py-1 rounded-full border border-white/10 font-mono">
                      {circuitMode} Mode
                    </span>
                 </div>
                 <CircuitRenderer expression={minimizedExpr} mode={circuitMode} />
              </div>

              {/* RTL Code Generation Terminal */}
              <div className="bg-[#0D121F]/90 backdrop-blur-xl border border-white/10 rounded-2xl p-6 shadow-2xl">
                 <div className="flex justify-between items-center mb-6">
                    <h3 className="text-xs font-mono font-semibold text-amber-200/70 uppercase tracking-widest flex items-center gap-2">
                      <Code2 size={16} className="text-fuchsia-400" /> Synthesized RTL Hardware Code
                    </h3>
                    <div className="flex bg-[#060911] rounded-xl p-1 border border-white/10 font-mono">
                      {['Verilog', 'VHDL'].map(lang => (
                        <button
                          key={lang}
                          onClick={() => setCodeLang(lang)}
                          className={`px-4 py-1.5 text-xs rounded-lg transition-all ${
                            codeLang === lang 
                              ? 'bg-slate-800 text-amber-300 font-semibold border border-amber-400/30 shadow-sm' 
                              : 'text-slate-500 hover:text-slate-300'
                          }`}
                        >
                          {lang}
                        </button>
                      ))}
                    </div>
                 </div>
                 
                 <TerminalWindow 
                    code={codeLang === 'Verilog' ? generateVerilog(numVars, minimizedExpr) : generateVHDL(numVars, minimizedExpr)} 
                    language={codeLang} 
                 />
              </div>

            </div>
          </div>

        </div>
      </div>

      <style dangerouslySetInnerHTML={{__html: `
        .custom-scrollbar::-webkit-scrollbar {
          width: 6px;
          height: 6px;
        }
        .custom-scrollbar::-webkit-scrollbar-track {
          background: #070A11; 
        }
        .custom-scrollbar::-webkit-scrollbar-thumb {
          background: #1E293B; 
          border-radius: 3px;
        }
        .custom-scrollbar::-webkit-scrollbar-thumb:hover {
          background: #334155; 
        }
      `}} />
    </div>
  );
}