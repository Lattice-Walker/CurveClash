/**
 * Maths War equation and terrain engine.
 *
 * This module deliberately has no DOM dependency. Pass the global math.js
 * object to compileEquation(), then hand the returned equation to
 * sampleEquation(). All coordinates returned by the sampler are canvas/world
 * coordinates (x grows right, y grows down); equations are evaluated in local
 * mathematical coordinates (x grows right, y grows up) around the shooter.
 */

const TAU = Math.PI * 2;
const EPSILON = 1e-9;

/**
 * Width in canvas pixels of one unit on the shooter's local mathematical axes.
 *
 * Equations are written in these units, not in pixels. Evaluating f(x) directly
 * on pixel coordinates makes every textbook function useless in a map-sized
 * window: log(x) climbs about seven pixels across an entire arena and exp(x)
 * turns vertical within seven pixels of the shooter, so both render as straight
 * lines. With a unit of fifty pixels a medium arena is roughly twenty-four by
 * fourteen units, which is the window a graphing calculator would use, and
 * sin(x), x^2 - 1, ln(x) and exp(x) - 1 all draw their familiar shapes.
 *
 * Only the local frame is scaled. Canvas, terrain, craters, hitboxes, and
 * scoring all stay in pixels.
 */
export const LOCAL_UNIT_PIXELS = 50;

function resolveUnitPixels(value) {
  const unit = Number(value ?? LOCAL_UNIT_PIXELS);
  return Number.isFinite(unit) && unit > 0 ? unit : LOCAL_UNIT_PIXELS;
}

// abs() is included so that absolute-value bars, which every graphing
// calculator accepts, have something to compile to.
const SAFE_FUNCTIONS = new Set([
  "abs", "acos", "acosh", "acot", "acoth", "acsc", "acsch", "asec",
  "asech", "asin", "asinh", "atan", "atan2", "atanh", "cbrt", "ceil",
  "cos", "cosh", "cot", "coth", "csc", "csch", "exp", "expm1", "fix",
  "floor", "hypot", "log", "log10", "log1p", "log2",
  "nthRoot", "pow", "round", "sec", "sech", "sign", "sin", "sinh",
  "sqrt", "tan", "tanh"
]);

const SAFE_SYMBOLS = new Set(["x", "e", "E", "pi", "PI", "tau", "Infinity"]);
const SAFE_NODE_TYPES = new Set([
  "ConstantNode", "FunctionNode", "OperatorNode", "ParenthesisNode", "SymbolNode"
]);

export class EquationError extends Error {
  constructor(message, code = "INVALID_EQUATION", cause = undefined) {
    super(message, cause ? { cause } : undefined);
    this.name = "EquationError";
    this.code = code;
  }
}

/**
 * LaTeX command names whose math.js spelling differs from the one a graphing
 * calculator prints. Everything not listed here simply loses its backslash,
 * which is already the right answer for \sin, \cos, \exp, \pi and friends.
 */
const LATEX_NAME_ALIASES = new Map([
  ["arcsin", "asin"], ["arccos", "acos"], ["arctan", "atan"],
  ["arccot", "acot"], ["arcsec", "asec"], ["arccsc", "acsc"],
  ["arsinh", "asinh"], ["arcosh", "acosh"], ["artanh", "atanh"],
  ["arcsinh", "asinh"], ["arccosh", "acosh"], ["arctanh", "atanh"],
  ["lg", "log10"], ["infty", "Infinity"],
  ["le", "\u2264"], ["leq", "\u2264"], ["ge", "\u2265"], ["geq", "\u2265"],
  ["ne", "\u2260"], ["neq", "\u2260"], ["lt", "<"], ["gt", ">"]
]);

/** Spacing and layout commands that carry no mathematical meaning. */
const LATEX_NOISE = /\\(?:displaystyle|textstyle|scriptstyle|limits|nolimits|quad|qquad|mathrm|mathit|text)\b|\\[,;:!]|\\ /g;

const SUPERSCRIPT_CHARACTERS = {
  "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4",
  "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9",
  "⁺": "+", "⁻": "-", "⁽": "(", "⁾": ")"
};
const SUPERSCRIPT_RUN = /[⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁽⁾]+/g;

// Sentinels for the two bar forms, kept apart from the bare `|` so that a
// \left|...\right| pair can nest while bare bars only alternate.
const ABS_OPEN = "\u0001";
const ABS_CLOSE = "\u0002";

/**
 * Convert common keyboard, Unicode and LaTeX notation into syntax understood
 * by math.js.
 *
 * The main source of LaTeX is a copy-paste out of Desmos, which writes every
 * bracket as \left...\right, every exponent and root argument as a brace
 * group, and every function name with a backslash, so
 * `\sin\left(x\right)+\sqrt{\left(x-10\right)^{2}}` has to come out as
 * `sin(x)+sqrt((x-10)^(2))`. Unicode superscripts (`x²`) and absolute-value
 * bars (`|x|`, `\left|x\right|`) are handled here too.
 */
export function cleanMathInput(value) {
  let text = String(value ?? "").trim()
    .replace(/^\$+|\$+$/g, "")
    .replace(LATEX_NOISE, " ")
    .replace(/\\cdot|\\times|[×·]/g, "*")
    .replace(/\\div|÷/g, "/")
    .replace(/[−–—]/g, "-")
    .replace(/π/g, "pi")
    .replace(/∞/g, "Infinity")
    .replace(/√/g, "\\sqrt")
    .replace(SUPERSCRIPT_RUN, (run) => `^(${[...run].map((c) => SUPERSCRIPT_CHARACTERS[c]).join("")})`)
    .replace(/\*\*/g, "^");

  text = stripLeftRight(text);
  text = text.replace(/\\operatorname\s*\{\s*([A-Za-z]+)\s*\}/g, "$1");
  text = expandLatexMacros(text);
  text = text.replace(/\\([A-Za-z]+)/g, (_match, name) => LATEX_NAME_ALIASES.get(name) ?? name);
  text = text.replace(/[{}]/g, (brace) => (brace === "{" ? "(" : ")"));
  text = convertAbsoluteBars(text);

  return text
    // math.js spells the natural logarithm log(); ln() is the notation most
    // players actually type, so accept it as an exact synonym. Rewriting whole
    // identifiers keeps names such as "sln" or "lnx" untouched.
    .replace(/[A-Za-z_][A-Za-z0-9_]*/g, (name) => (name === "ln" ? "log" : name))
    // `x\left(x+1\right)` is a product to a calculator but a call to a parser,
    // so a variable standing in front of a bracket gets its multiplication
    // sign back. Function names are left alone: sin(x) really is a call.
    .replace(/([A-Za-z_][A-Za-z0-9_]*)\s*\(/g, (match, name) => (
      SAFE_SYMBOLS.has(name) ? `${name}*(` : match
    ))
    .replace(/\s+/g, " ")
    .trim();
}

/**
 * Drop \left and \right, keeping the delimiter they size. Bars become
 * sentinels so the absolute-value pass can tell an explicitly paired bar from
 * a bare one, and \left. / \right. vanish entirely.
 */
function stripLeftRight(text) {
  return text
    .replace(/\\left\s*\|/g, ABS_OPEN)
    .replace(/\\right\s*\|/g, ABS_CLOSE)
    .replace(/\\(?:left|right)\s*\\?([([{)\]}.])/g, (_match, delimiter) => {
      if (delimiter === ".") return "";
      if (delimiter === "{" || delimiter === "[") return "(";
      if (delimiter === "}" || delimiter === "]") return ")";
      return delimiter;
    })
    .replace(/\\(?:left|right)\b/g, "");
}

/**
 * Rewrite the LaTeX macros that take brace arguments -- \frac and \sqrt --
 * into calls. They are the only ones whose meaning depends on where their
 * arguments end, so they need a brace matcher rather than a regex.
 */
function expandLatexMacros(text) {
  let out = "";
  let index = 0;
  while (index < text.length) {
    const fraction = /^\\[dt]?frac/.exec(text.slice(index));
    if (fraction) {
      const numerator = readLatexArgument(text, index + fraction[0].length);
      const denominator = readLatexArgument(text, numerator.end);
      out += `((${expandLatexMacros(numerator.body)})/(${expandLatexMacros(denominator.body)}))`;
      index = denominator.end;
      continue;
    }
    const root = /^\\sqrt/.exec(text.slice(index));
    if (root) {
      let cursor = index + root[0].length;
      let degree = null;
      if (text[cursor] === "[") {
        const close = text.indexOf("]", cursor);
        if (close !== -1) {
          degree = text.slice(cursor + 1, close);
          cursor = close + 1;
        }
      }
      const radicand = readLatexArgument(text, cursor);
      out += degree === null
        ? `sqrt(${expandLatexMacros(radicand.body)})`
        : `nthRoot((${expandLatexMacros(radicand.body)}), (${expandLatexMacros(degree)}))`;
      index = radicand.end;
      continue;
    }
    out += text[index];
    index += 1;
  }
  return out;
}

/**
 * Read one LaTeX argument starting at `start`: a bracketed group, a command,
 * or the single character that `\sqrt2` and `\frac12` rely on.
 */
function readLatexArgument(text, start) {
  let index = start;
  while (index < text.length && /\s/.test(text[index])) index += 1;
  if (index >= text.length) return { body: "", end: index };

  // A brace group is the LaTeX form; a bracket group is what a hand-typed
  // radical sign produces, since it is rewritten to \sqrt before this runs.
  const closer = { "{": "}", "(": ")", "[": "]" }[text[index]];
  if (closer) {
    const opener = text[index];
    let depth = 0;
    for (let scan = index; scan < text.length; scan += 1) {
      if (text[scan] === opener) depth += 1;
      else if (text[scan] === closer) {
        depth -= 1;
        if (depth === 0) return { body: text.slice(index + 1, scan), end: scan + 1 };
      }
    }
    // Unbalanced brackets: take the rest and let math.js report the problem.
    return { body: text.slice(index + 1), end: text.length };
  }

  const command = /^\\[A-Za-z]+/.exec(text.slice(index));
  if (command) return { body: command[0], end: index + command[0].length };
  return { body: text[index], end: index + 1 };
}

/**
 * Turn absolute-value bars into abs() calls. Explicit \left|...\right| pairs
 * nest; bare bars alternate open/close, which is the only reading available
 * without knowing what the author meant by `|x|y|`.
 */
function convertAbsoluteBars(text) {
  const endsValue = (emitted) => /[0-9A-Za-z_.)\]]$/.test(emitted);
  let out = "";
  let bareOpen = false;

  for (let index = 0; index < text.length; index += 1) {
    const character = text[index];
    const isBare = character === "|";
    if (character !== ABS_OPEN && character !== ABS_CLOSE && !isBare) {
      out += character;
      continue;
    }

    const opening = character === ABS_OPEN || (isBare && !bareOpen);
    if (isBare) bareOpen = !bareOpen;

    if (opening) {
      if (endsValue(out)) out += "*";
      out += "abs(";
    } else {
      out += ")";
      const next = text[index + 1];
      if (next && /[0-9A-Za-z_.([]/.test(next)) out += "*";
    }
  }

  // An unclosed bar would otherwise become an unbalanced parenthesis.
  if (bareOpen) out += ")";
  return out;
}

/**
 * Accept a right-hand expression as the primary player input. The interface
 * supplies the visible `f(x) =` prefix. Full `f(x) = expression` input remains
 * accepted for bot output and pasted equations, as does the `y = expression`
 * a graphing calculator writes, while every other equality is rejected. Blank
 * input remains the timer-expiry null shot.
 */
export function normalizeEquation(source) {
  const cleaned = cleanMathInput(source);
  if (/[<>\u2264\u2265\u2260]/.test(cleaned)) {
    throw new EquationError(
      "A shot is a function of x, so an inequality cannot be fired. Type only the expression after f(x) =.",
      "FUNCTION_FORM_REQUIRED"
    );
  }
  if (!cleaned) {
    return {
      kind: "null",
      source: "",
      display: "",
      expression: "0"
    };
  }

  const pieces = cleaned.split("=");
  if (pieces.length > 2) {
    throw new EquationError(
      "Type only the expression after f(x) =. Multiple equalities are not allowed.",
      "FUNCTION_FORM_REQUIRED"
    );
  }

  let expression;
  if (pieces.length === 1) {
    expression = pieces[0].trim();
  } else {
    const left = pieces[0].trim();
    expression = pieces[1].trim();
    // `y = ...` is how a graphing calculator names the same function, so a
    // paste keeps its left-hand side; every other equality is still refused.
    if (!/^(?:f\s*\(\s*x\s*\)|y)$/.test(left)) {
      throw new EquationError(
        "Type only the expression after f(x) =. Another equals sign is not allowed.",
        "FUNCTION_FORM_REQUIRED"
      );
    }
  }

  if (!expression) {
    throw new EquationError(
      "Enter an expression after f(x) =, for example x^2 - 1.",
      "INCOMPLETE_EQUATION"
    );
  }
  if (containsVariable(expression, "y")) {
    throw new EquationError(
      "The right-hand side of f(x) may use x, but it cannot use y.",
      "FUNCTION_USES_Y"
    );
  }

  return {
    kind: "cartesian",
    source: cleaned,
    display: `f(x) = ${expression}`,
    expression
  };
}

function containsVariable(expression, variable) {
  const escaped = variable.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(`(^|[^A-Za-z0-9_])${escaped}([^A-Za-z0-9_]|$)`).test(expression);
}

/** Parse, validate and compile a normalized expression using math.js. */
export function compileEquation(source, mathLib = globalThis.math, options = {}) {
  const unit = resolveUnitPixels(options.unitPixels);
  const normalized = typeof source === "string" ? normalizeEquation(source) : source;
  if (!normalized || normalized.kind === "null") {
    return {
      ...(normalized ?? normalizeEquation("")),
      node: null,
      compiled: null,
      unitPixels: unit,
      evaluateLocal: () => Number.NaN
    };
  }
  if (normalized.kind !== "cartesian") {
    throw new EquationError(
      "Only a one-variable expression for f(x) is allowed.",
      "FUNCTION_FORM_REQUIRED"
    );
  }
  if (!mathLib || typeof mathLib.parse !== "function") {
    throw new EquationError("math.js is required to compile equations.", "MATHJS_MISSING");
  }

  try {
    const node = mathLib.parse(normalized.expression);
    validateMathNode(node, normalized.kind);
    const compiled = node.compile();
    const reusableScope = { x: 0, tau: TAU };
    // The whole engine downstream — sampling, root finding, collision — speaks
    // pixels, so the unit conversion is folded into evaluation itself: take a
    // pixel abscissa in, hand a pixel ordinate back, and let the author's
    // expression see only local units.
    const evaluateAtPixel = (xPixels) => {
      reusableScope.x = xPixels / unit;
      return toFiniteNumber(compiled.evaluate(reusableScope)) * unit;
    };
    return {
      ...normalized,
      node,
      compiled,
      unitPixels: unit,
      evaluateLocal(x, _y = 0) {
        return evaluateAtPixel(x);
      },
      evaluateContourLocal(x, _y = 0) {
        return evaluateAtPixel(x);
      }
    };
  } catch (error) {
    if (error instanceof EquationError) throw error;
    throw new EquationError(`Could not understand this equation: ${error.message}`, "PARSE_ERROR", error);
  }
}

function validateMathNode(root, kind) {
  let nodeCount = 0;
  root.traverse((node, _path, parent) => {
    nodeCount += 1;
    if (nodeCount > 220) {
      throw new EquationError("This equation is too complex for a turn.", "TOO_COMPLEX");
    }
    if (!SAFE_NODE_TYPES.has(node.type)) {
      throw new EquationError(`Unsupported expression element: ${node.type}.`, "UNSAFE_EXPRESSION");
    }
    if (node.type === "SymbolNode") {
      const parentIsFunctionName = parent?.type === "FunctionNode" && parent.fn === node;
      if (!parentIsFunctionName && !SAFE_SYMBOLS.has(node.name)) {
        throw new EquationError(`Unknown symbol “${node.name}”. Only x may vary.`, "UNKNOWN_SYMBOL");
      }
      if (kind === "cartesian" && node.name === "y") {
        throw new EquationError("The right-hand side of f(x) cannot use y.", "FUNCTION_USES_Y");
      }
    }
    if (node.type === "FunctionNode") {
      const name = node.fn?.name ?? node.name;
      if (!SAFE_FUNCTIONS.has(name)) {
        throw new EquationError(`Function “${name}” is not available in the game.`, "UNKNOWN_FUNCTION");
      }
    }
  });
}

/** Friendly facade used by the game layer. */
export function parseEquation(source, mathLib = globalThis.math, options = {}) {
  return compileEquation(source, mathLib, options);
}

/** Produce KaTeX-ready LaTeX without introducing a KaTeX dependency here. */
/**
 * Render an equation for display.
 *
 * `options.significantDigits` rounds the numbers on the way to LaTeX, for
 * screens where a curve is being read rather than reproduced: a bot's fitted
 * coefficients carry ten digits, and `-9.098564556556x` tells a player far
 * less about the shot than `-9.1x` does. The rounding is applied to a copy of
 * the syntax tree, so it never reaches the compiled function that is actually
 * fired — and when it changes anything the relation is rendered as `≈`, so a
 * displayed curve never claims to be exact when it is not.
 */
export function equationToLatex(equationOrSource, mathLib = globalThis.math, options = {}) {
  const equation = typeof equationOrSource === "string"
    ? compileEquation(equationOrSource, mathLib)
    : equationOrSource;
  if (!equation || equation.kind === "null") return "\\varnothing";

  if (equation.kind === "cartesian") {
    const rounded = roundNodeForDisplay(equation.node, options.significantDigits, mathLib);
    const right = rounded.node?.toTex
      ? rounded.node.toTex({ parenthesis: "keep" })
      : equation.expression;
    return `f\\left(x\\right) ${rounded.changed ? "\\approx" : "="} ${right}`;
  }

  // Preserve the equality the player entered rather than rendering the
  // internally normalized `(left) - (right) = 0` form.
  const display = equation.display || equation.source || `${equation.expression} = 0`;
  const sides = display.split("=");
  if (sides.length === 2 && mathLib?.parse) {
    try {
      const left = mathLib.parse(sides[0].trim()).toTex({ parenthesis: "keep" });
      const right = mathLib.parse(sides[1].trim()).toTex({ parenthesis: "keep" });
      return `${left} = ${right}`;
    } catch {
      // Fall back to the readable normalized text below.
    }
  }
  return display;
}

/**
 * Copy a syntax tree with every number reduced to `digits` significant
 * figures. Significant figures rather than decimal places because the
 * coefficients here span several orders of magnitude — a parabola's leading
 * term is a fraction of a pixel while a cubic's normalising divisor is tens
 * of them, and a fixed number of decimals would flatten one to nothing while
 * leaving the other just as long as before.
 */
function roundNodeForDisplay(node, digits, mathLib) {
  const places = Math.floor(Number(digits));
  if (!node?.transform || !(places >= 1) || typeof mathLib?.ConstantNode !== "function") {
    return { node, changed: false };
  }
  let changed = false;
  const rounded = node.transform((current) => {
    if (current.type !== "ConstantNode") return current;
    const value = toFiniteNumber(current.value);
    if (!Number.isFinite(value) || value === 0) return current;
    // toPrecision never collapses a non-zero to zero, so a genuinely tiny
    // coefficient keeps its magnitude instead of vanishing from the curve.
    const approximation = Number(value.toPrecision(places));
    if (approximation === value) return current;
    changed = true;
    return new mathLib.ConstantNode(approximation);
  });
  return { node: rounded, changed };
}

function toFiniteNumber(value) {
  if (typeof value === "number") return Number.isFinite(value) ? value : Number.NaN;
  if (value && typeof value.re === "number" && typeof value.im === "number") {
    return Math.abs(value.im) <= EPSILON && Number.isFinite(value.re) ? value.re : Number.NaN;
  }
  if (value && typeof value.valueOf === "function") {
    const primitive = value.valueOf();
    return typeof primitive === "number" && Number.isFinite(primitive) ? primitive : Number.NaN;
  }
  return Number.NaN;
}

export function makeBounds(width, height) {
  return { x: 0, y: 0, width, height };
}

function normalizedBounds(bounds) {
  const x = Number(bounds?.x ?? 0);
  const y = Number(bounds?.y ?? 0);
  const width = Number(bounds?.width ?? 0);
  const height = Number(bounds?.height ?? 0);
  if (!(width > 0 && height > 0)) throw new TypeError("bounds must have positive width and height");
  return { x, y, width, height, right: x + width, bottom: y + height };
}

export function localToWorld(point, origin, unitPixels = LOCAL_UNIT_PIXELS) {
  const unit = resolveUnitPixels(unitPixels);
  return { x: origin.x + point.x * unit, y: origin.y - point.y * unit };
}

export function worldToLocal(point, origin, unitPixels = LOCAL_UNIT_PIXELS) {
  const unit = resolveUnitPixels(unitPixels);
  return { x: (point.x - origin.x) / unit, y: (origin.y - point.y) / unit };
}

// Acceptance band for |f(0)|, measured in world pixels (evaluateLocal returns a
// pixel ordinate). A millionth of a pixel is visually exact while leaving room
// for the rounding an expression that is mathematically zero at the origin can
// still pick up, e.g. 2 * sin(x / 1.5) evaluated through math.js.
const ORIGIN_ZERO_TOLERANCE = 1e-6;

/**
 * Require that an f(x) function passes through y = 0 at x = 0, i.e. starts on
 * the shooter. `minimumX`/`maximumX` are accepted so the call reads next to the
 * playable-range bounds the sampler already computes, but they are not
 * consulted: the only requirement is the value at the origin.
 */
export function assertPlayableFunctionZero(equation, minimumX, maximumX, options = {}) {
  const valueAtOrigin = safelyEvaluateAt(equation, 0);
  const tolerance = Number(options.originZeroTolerance ?? ORIGIN_ZERO_TOLERANCE);
  if (!Number.isFinite(valueAtOrigin) || Math.abs(valueAtOrigin) > tolerance) {
    const message = isNeverZeroNode(equation?.node)
      ? "This function is never 0, so it cannot pass through the origin. Shift it down by its value at x = 0, for example exp(x / 3) - 1."
      : "This function must pass through y = 0 at x = 0, for example x^2 + 3 * x or 2 * x.";
    throw new EquationError(message, "NO_ORIGIN_ZERO");
  }
  return { x: 0, value: 0, method: "origin" };
}

function safelyEvaluateAt(equation, x) {
  try {
    const value = equation.evaluateLocal(x, 0);
    return Number.isFinite(value) ? value : Number.NaN;
  } catch {
    return Number.NaN;
  }
}

/**
 * Report expressions that are mathematically never zero, such as exp(x), 10^x
 * or 2 * e^x. This only sharpens the rejection message for a bare exponential;
 * the origin check itself already refuses anything with a non-zero f(0). The
 * walk is deliberately conservative: anything it cannot prove non-zero returns
 * false and falls back to the generic message.
 */
function isNeverZeroNode(node) {
  let current = node;
  while (current?.type === "ParenthesisNode") current = current.content;
  if (!current) return false;

  if (current.type === "ConstantNode") {
    const value = toFiniteNumber(current.value);
    return Number.isFinite(value) && value !== 0;
  }
  if (current.type === "SymbolNode") {
    return current.name === "e" || current.name === "E"
      || current.name === "pi" || current.name === "PI" || current.name === "tau";
  }
  if (current.type === "FunctionNode") {
    return (current.fn?.name ?? current.name) === "exp";
  }
  if (current.type === "OperatorNode") {
    const operands = current.args ?? [];
    if (current.fn === "unaryMinus" || current.fn === "unaryPlus") {
      return isNeverZeroNode(operands[0]);
    }
    if (current.fn === "multiply" || current.fn === "divide") {
      return operands.length === 2 && operands.every((operand) => isNeverZeroNode(operand));
    }
    if (current.fn === "pow") {
      // A strictly positive constant base stays positive for every real
      // exponent, however small the double-precision result becomes.
      return operands.length === 2 && isPositiveConstantNode(operands[0]);
    }
  }
  return false;
}

function isPositiveConstantNode(node) {
  let current = node;
  while (current?.type === "ParenthesisNode") current = current.content;
  if (!current) return false;
  if (current.type === "ConstantNode") {
    const value = toFiniteNumber(current.value);
    return Number.isFinite(value) && value > 0;
  }
  if (current.type === "SymbolNode") {
    return ["e", "E", "pi", "PI", "tau"].includes(current.name);
  }
  if (current.type === "OperatorNode" && (current.fn === "multiply" || current.fn === "divide")) {
    return (current.args ?? []).length === 2 && current.args.every((operand) => isPositiveConstantNode(operand));
  }
  return false;
}

/**
 * Sample an accepted f(x) equation into ordered world-space branches.
 * Return shape: `{ kind, branches, components, diagnostics }`.
 */
export function sampleEquation(equation, origin, bounds, options = {}) {
  if (!equation || equation.kind === "null") {
    return { kind: "null", branches: [], components: [], diagnostics: { sampleCount: 0 } };
  }
  const resolvedOrigin = origin?.position ?? origin;
  if (!resolvedOrigin || !Number.isFinite(resolvedOrigin.x) || !Number.isFinite(resolvedOrigin.y)) {
    throw new TypeError("origin must be a finite {x, y} point");
  }
  const area = normalizedBounds(bounds);
  if (equation.kind === "cartesian") {
    const requirePlayableZero = options.requirePlayableZero !== false && options.requireZeroCrossing !== false;
    const playableZero = requirePlayableZero
      ? assertPlayableFunctionZero(
        equation,
        area.x - resolvedOrigin.x,
        area.right - resolvedOrigin.x,
        options
      )
      : null;
    const sampled = sampleCartesian(equation, resolvedOrigin, area, options);
    sampled.diagnostics.playableZero = playableZero;
    return sampled;
  }
  throw new EquationError(
    "Only a one-variable expression for f(x) is allowed.",
    "FUNCTION_FORM_REQUIRED"
  );
}

function sampleCartesian(equation, origin, bounds, options) {
  const step = clamp(Number(options.step ?? 3), 0.5, 20);
  const maxSamples = Math.max(50, Math.floor(options.maxSamples ?? 12000));
  const maxJump = Number(options.discontinuityJump ?? Math.max(bounds.height * 0.7, 240));
  const xLimits = [origin.x - bounds.x, bounds.right - origin.x];
  const rawBranches = [];
  // The first in-arena run found walking outward from the shooter, one per
  // direction. That run is the shot; anything past a gap is preview only.
  const primaryBranches = [];
  let sampleCount = 0;

  for (const direction of [-1, 1]) {
    const limit = direction < 0 ? xLimits[0] : xLimits[1];
    let current = [];
    let previous = null;
    let emittedInDirection = 0;
    const emitCurrentBranch = () => {
      if (current.length > 1) {
        rawBranches.push(current);
        if (emittedInDirection === 0) primaryBranches.push(current);
        emittedInDirection += 1;
      }
      current = [];
    };

    for (let distance = 0; distance <= limit + step && sampleCount < maxSamples; distance += step) {
      const localX = distance * direction;
      const localY = equation.evaluateLocal(localX, 0);
      sampleCount += 1;
      if (!Number.isFinite(localY)) {
        emitCurrentBranch();
        previous = null;
        // A trajectory cannot jump across an undefined point. Keep scanning so
        // preview diagnostics preserve later components, but they form a new branch.
        continue;
      }

      const point = { x: origin.x + localX, y: origin.y - localY };
      if (previous && Math.abs(point.y - previous.y) > maxJump) {
        emitCurrentBranch();
      }
      if (!current.length || squaredDistance(current[current.length - 1], point) > EPSILON) {
        current.push(point);
      }
      previous = point;

      // Keep one outside sample so traceEquation can terminate exactly at the edge.
      if (!pointInBounds(point, bounds, 0) && distance > 0) {
        emitCurrentBranch();
        previous = null;
        // A function with a vertical asymptote at the shooter — ln(x) is the
        // everyday case — is off the map for its first fraction of a pixel and
        // only enters further out. Keep scanning until the curve has been
        // inside once; after that, leaving the arena ends the shot.
        if (emittedInDirection) break;
        continue;
      }
    }
    emitCurrentBranch();
  }

  // Walking outward from the shooter, the first arena-crossing run in each
  // direction is the official shot; later runs sit behind a pole or an
  // undefined stretch and stay preview-only. This covers f(0) = 0, an
  // f(0) that is merely non-zero, and an f(0) that does not exist at all.
  const official = primaryBranches;
  return {
    kind: "cartesian",
    branches: official,
    components: rawBranches,
    diagnostics: {
      sampleCount,
      anchored: false,
      disconnectedComponents: Math.max(0, rawBranches.length - official.length)
    }
  };
}

function sampleImplicit(equation, origin, bounds, options) {
  const step = clamp(Number(options.implicitStep ?? options.step ?? 6), 2, 24);
  const maxCells = Math.max(1000, Math.floor(options.maxCells ?? 60000));
  let columns = Math.ceil(bounds.width / step);
  let rows = Math.ceil(bounds.height / step);
  const cellCount = columns * rows;
  if (cellCount > maxCells) {
    const scale = Math.sqrt(cellCount / maxCells);
    columns = Math.ceil(columns / scale);
    rows = Math.ceil(rows / scale);
  }
  const dx = bounds.width / columns;
  const dy = bounds.height / rows;
  const values = new Float64Array((columns + 1) * (rows + 1));
  let evaluationCount = 0;
  const evaluateContour = equation.evaluateContourLocal ?? equation.evaluateLocal;

  for (let row = 0; row <= rows; row += 1) {
    const worldY = bounds.y + row * dy;
    for (let column = 0; column <= columns; column += 1) {
      const worldX = bounds.x + column * dx;
      values[row * (columns + 1) + column] = evaluateContour(worldX - origin.x, origin.y - worldY);
      evaluationCount += 1;
    }
  }

  const segments = [];
  for (let row = 0; row < rows; row += 1) {
    for (let column = 0; column < columns; column += 1) {
      const corners = [
        { x: bounds.x + column * dx, y: bounds.y + row * dy },
        { x: bounds.x + (column + 1) * dx, y: bounds.y + row * dy },
        { x: bounds.x + (column + 1) * dx, y: bounds.y + (row + 1) * dy },
        { x: bounds.x + column * dx, y: bounds.y + (row + 1) * dy }
      ];
      const stride = columns + 1;
      const cellValues = [
        values[row * stride + column],
        values[row * stride + column + 1],
        values[(row + 1) * stride + column + 1],
        values[(row + 1) * stride + column]
      ];
      const cellSegments = [];
      addMarchingSquareSegments(cellSegments, corners, cellValues);
      for (const segment of cellSegments) {
        if (options.validateContinuity === false || isContinuousZeroSegment(segment, evaluateContour, origin, dx, dy)) {
          segments.push(segment);
        }
      }
    }
  }

  const joinTolerance = Math.max(0.02, Math.min(dx, dy) * 0.08);
  const chainedComponents = chainSegments(segments, joinTolerance);
  // A lone two-point fragment is normally a quantization artifact from an
  // ambiguous grid cell. Keep it only when it is the sole contour available.
  const components = chainedComponents.length > 1
    ? chainedComponents.filter((points) => points.length > 2)
    : chainedComponents;
  const originTolerance = Number(options.originTolerance ?? Math.max(dx, dy) * 2.1);
  const ordered = components
    .map((points) => ({ points, distance2: polylineDistanceSquared(points, origin) }))
    .sort((a, b) => a.distance2 - b.distance2);
  let selected;
  if (options.implicitMode === "all") {
    selected = ordered;
  } else {
    selected = ordered.filter((entry) => entry.distance2 <= originTolerance ** 2);
    // Some valid implicit curves (for example x^2+y^2=10000) do not cross the
    // local origin. They must still animate, so use the nearest component unless
    // a caller explicitly requests origin-connected contours only.
    if (!selected.length && options.allowDetachedImplicit !== false) selected = ordered.slice(0, 1);
  }

  const branches = [];
  for (const entry of selected) {
    branches.push(...splitPolylineAtNearest(entry.points, origin, originTolerance));
  }

  return {
    kind: "implicit",
    branches,
    components,
    diagnostics: {
      cellCount: columns * rows,
      evaluationCount,
      segmentCount: segments.length,
      componentCount: components.length,
      selectedComponentCount: selected.length,
      gridStep: { x: dx, y: dy }
    }
  };
}

/**
 * A sign flip across a pole is not a zero (for example 1/x = 0). Validate each
 * interpolated contour along its estimated normal: a real zero is much closer
 * to zero than samples on both sides, whereas an asymptote-generated segment
 * is not. This also rejects non-finite poles before they can hit or crater.
 */
function isContinuousZeroSegment(segment, evaluateContour, origin, dx, dy) {
  const start = segment[0];
  const end = segment[1];
  const midpoint = { x: (start.x + end.x) / 2, y: (start.y + end.y) / 2 };
  const tangentX = end.x - start.x;
  const tangentY = end.y - start.y;
  const length = Math.hypot(tangentX, tangentY);
  if (!(length > EPSILON)) return false;

  const normalX = -tangentY / length;
  const normalY = tangentX / length;
  const offset = Math.max(0.35, Math.min(dx, dy) * 0.22);
  const toLocalPixels = (point) => ({ x: point.x - origin.x, y: origin.y - point.y });
  const localMidpoint = toLocalPixels(midpoint);
  const localPlus = toLocalPixels({ x: midpoint.x + normalX * offset, y: midpoint.y + normalY * offset });
  const localMinus = toLocalPixels({ x: midpoint.x - normalX * offset, y: midpoint.y - normalY * offset });
  const centerValue = evaluateContour(localMidpoint.x, localMidpoint.y);
  const plusValue = evaluateContour(localPlus.x, localPlus.y);
  const minusValue = evaluateContour(localMinus.x, localMinus.y);
  if (![centerValue, plusValue, minusValue].every(Number.isFinite)) return false;

  const centerMagnitude = Math.abs(centerValue);
  const normalMagnitude = Math.min(Math.abs(plusValue), Math.abs(minusValue));
  return centerMagnitude <= Math.max(1e-8, normalMagnitude * 0.95);
}

function addMarchingSquareSegments(output, corners, values) {
  if (values.some((value) => !Number.isFinite(value))) return;
  let mask = 0;
  for (let index = 0; index < 4; index += 1) {
    if (values[index] >= 0) mask |= 1 << index;
  }
  if (mask === 0 || mask === 15) {
    // All exact-zero cells are ignored; drawing their perimeter creates large,
    // artificial rectangles for equations that are zero over an area.
    return;
  }

  const edgeCorners = [[0, 1], [1, 2], [2, 3], [3, 0]];
  const intersections = new Array(4);
  const pointOnEdge = (edge) => {
    if (intersections[edge]) return intersections[edge];
    const [a, b] = edgeCorners[edge];
    const va = values[a];
    const vb = values[b];
    const denominator = va - vb;
    const amount = Math.abs(denominator) < EPSILON ? 0.5 : clamp(va / denominator, 0, 1);
    intersections[edge] = lerpPoint(corners[a], corners[b], amount);
    return intersections[edge];
  };
  const connect = (edgeA, edgeB) => output.push([pointOnEdge(edgeA), pointOnEdge(edgeB)]);

  const simpleCases = {
    1: [3, 0], 2: [0, 1], 3: [3, 1], 4: [1, 2],
    6: [0, 2], 7: [3, 2], 8: [2, 3], 9: [0, 2],
    11: [1, 2], 12: [3, 1], 13: [0, 1], 14: [3, 0]
  };
  if (simpleCases[mask]) {
    connect(...simpleCases[mask]);
    return;
  }

  // Ambiguous saddle cases use the center value (asymptotic-decider style)
  // so adjacent branches are not connected arbitrarily.
  const centerPositive = values.reduce((sum, value) => sum + value, 0) >= 0;
  if ((mask === 5 && centerPositive) || (mask === 10 && !centerPositive)) {
    connect(0, 1);
    connect(2, 3);
  } else {
    connect(3, 0);
    connect(1, 2);
  }
}

function chainSegments(segments, tolerance) {
  if (!segments.length) return [];
  const endpointMap = new Map();
  const keys = segments.map((segment, segmentIndex) => segment.map((point, end) => {
    const key = `${Math.round(point.x / tolerance)},${Math.round(point.y / tolerance)}`;
    const entries = endpointMap.get(key) ?? [];
    entries.push({ segmentIndex, end });
    endpointMap.set(key, entries);
    return key;
  }));
  const visited = new Uint8Array(segments.length);
  const components = [];

  const walk = (startIndex, startEnd) => {
    const path = [];
    let segmentIndex = startIndex;
    let enterEnd = startEnd;
    while (!visited[segmentIndex]) {
      visited[segmentIndex] = 1;
      const segment = segments[segmentIndex];
      const exitEnd = enterEnd === 0 ? 1 : 0;
      if (!path.length) path.push(segment[enterEnd]);
      path.push(segment[exitEnd]);
      const candidates = endpointMap.get(keys[segmentIndex][exitEnd]) ?? [];
      const next = candidates.find((candidate) => !visited[candidate.segmentIndex]);
      if (!next) break;
      segmentIndex = next.segmentIndex;
      enterEnd = next.end;
    }
    return deduplicateAdjacent(path);
  };

  // Open polylines first, then closed loops.
  for (let index = 0; index < segments.length; index += 1) {
    if (visited[index]) continue;
    const degree0 = endpointMap.get(keys[index][0])?.length ?? 0;
    const degree1 = endpointMap.get(keys[index][1])?.length ?? 0;
    if (degree0 === 1 || degree1 === 1) {
      const path = walk(index, degree0 === 1 ? 0 : 1);
      if (path.length > 1) components.push(path);
    }
  }
  for (let index = 0; index < segments.length; index += 1) {
    if (visited[index]) continue;
    const path = walk(index, 0);
    if (path.length > 1) components.push(path);
  }
  return components;
}

function splitPolylineAtNearest(points, origin, snapTolerance) {
  if (points.length < 2) return [];
  const closed = squaredDistance(points[0], points[points.length - 1]) <= 1;
  if (closed && points.length > 4) {
    const cycle = points.slice(0, -1);
    let nearestIndex = 0;
    for (let index = 1; index < cycle.length; index += 1) {
      if (squaredDistance(cycle[index], origin) < squaredDistance(cycle[nearestIndex], origin)) {
        nearestIndex = index;
      }
    }
    const start = squaredDistance(cycle[nearestIndex], origin) <= snapTolerance ** 2
      ? { ...origin }
      : cycle[nearestIndex];
    const half = Math.ceil(cycle.length / 2);
    const clockwise = [start];
    const counterClockwise = [start];
    for (let offset = 1; offset <= half; offset += 1) {
      clockwise.push(cycle[(nearestIndex + offset) % cycle.length]);
      counterClockwise.push(cycle[(nearestIndex - offset + cycle.length) % cycle.length]);
    }
    return [deduplicateAdjacent(clockwise), deduplicateAdjacent(counterClockwise)].filter((p) => p.length > 1);
  }

  let nearest = { distance2: Infinity, segment: 0, amount: 0, point: points[0] };
  for (let index = 0; index < points.length - 1; index += 1) {
    const projection = projectPointToSegment(origin, points[index], points[index + 1]);
    if (projection.distance2 < nearest.distance2) {
      nearest = { ...projection, segment: index };
    }
  }
  const pivot = nearest.distance2 <= snapTolerance ** 2 ? { ...origin } : nearest.point;
  const forward = deduplicateAdjacent([pivot, ...points.slice(nearest.segment + 1)]);
  const backward = deduplicateAdjacent([pivot, ...points.slice(0, nearest.segment + 1).reverse()]);
  return [forward, backward].filter((branch) => branch.length > 1);
}

/**
 * Follow sampled branches at sub-pixel intervals. Players never stop a trace;
 * solid terrain and map bounds do. Hits are unique across every branch.
 */
export function traceEquation({
  branches,
  terrain = null,
  players = [],
  shooterId = null,
  bounds,
  hitRadius = 26,
  collisionStep = 0.8
}) {
  const area = normalizedBounds(bounds);
  const step = clamp(Number(collisionStep), 0.25, 4);
  const hitIds = new Set();
  const hitEvents = [];
  const impacts = [];
  const tracedBranches = [];

  for (let branchIndex = 0; branchIndex < (branches ?? []).length; branchIndex += 1) {
    const source = branches[branchIndex];
    if (!source || source.length < 2) continue;
    // Some sampled branches can be discarded after immediately touching solid
    // terrain. Events must point at the compact output array, not the original
    // sampled index, or animation timing will reference the wrong path.
    const outputBranchIndex = tracedBranches.length;
    const traced = [];
    const branchHitIds = new Set(hitIds);
    const branchHitEvents = [];
    const branchImpacts = [];
    let stopped = false;
    let previous = source[0];

    if (pointInBounds(previous, area) && !isTerrainBlocked(terrain, previous.x, previous.y)) {
      traced.push({ ...previous });
      collectHits(previous, players, shooterId, hitRadius, branchHitIds, branchHitEvents, outputBranchIndex, 0);
    }

    for (let pointIndex = 1; pointIndex < source.length && !stopped; pointIndex += 1) {
      const next = source[pointIndex];
      const length = Math.hypot(next.x - previous.x, next.y - previous.y);
      const subdivisions = Math.max(1, Math.ceil(length / step));
      for (let sample = 1; sample <= subdivisions; sample += 1) {
        const amount = sample / subdivisions;
        const point = lerpPoint(previous, next, amount);
        if (!pointInBounds(point, area)) {
          const boundary = traced.length
            ? segmentBoundaryIntersection(traced[traced.length - 1], point, area)
            : null;
          if (boundary) traced.push(boundary);
          branchImpacts.push({ type: "boundary", point: boundary ?? point, branchIndex: outputBranchIndex });
          stopped = true;
          break;
        }
        if (isTerrainBlocked(terrain, point.x, point.y)) {
          const lastFree = traced[traced.length - 1] ?? lerpPoint(previous, next, (sample - 1) / subdivisions);
          const contact = refineTerrainContact(terrain, lastFree, point);
          if (traced.length && squaredDistance(traced[traced.length - 1], contact.lastFree) > 1e-8) {
            traced.push(contact.lastFree);
            collectHits(
              contact.lastFree,
              players,
              shooterId,
              hitRadius,
              branchHitIds,
              branchHitEvents,
              outputBranchIndex,
              traced.length - 1
            );
          }
          branchImpacts.push({
            type: "terrain",
            // Keep the crater center infinitesimally inside solid terrain while
            // exposing the exact visible endpoint for renderers.
            point: contact.firstBlocked,
            pathEnd: contact.lastFree,
            branchIndex: outputBranchIndex
          });
          stopped = true;
          break;
        }
        traced.push(point);
        collectHits(point, players, shooterId, hitRadius, branchHitIds, branchHitEvents, outputBranchIndex, traced.length - 1);
      }
      previous = next;
    }
    if (traced.length > 1) {
      tracedBranches.push(traced);
      for (const playerId of branchHitIds) hitIds.add(playerId);
      hitEvents.push(...branchHitEvents);
      impacts.push(...branchImpacts);
    }
  }

  return {
    branches: tracedBranches,
    hitIds: [...hitIds],
    hitEvents,
    impacts,
    firstTerrainImpact: impacts.find((impact) => impact.type === "terrain") ?? null
  };
}

/**
 * High-level facade: parse (if needed), sample, then terrain-clip and hit-test.
 * This is the main function the UI needs for both live previews and shots.
 */
export function buildCurvePlan(
  equationOrSource,
  origin,
  bounds,
  obstacleField = null,
  options = {}
) {
  const resolvedOrigin = origin?.position ?? origin;
  const equation = typeof equationOrSource === "string"
    ? parseEquation(equationOrSource, options.math ?? globalThis.math)
    : equationOrSource;
  const sampled = sampleEquation(equation, resolvedOrigin, bounds, options);
  const traced = traceEquation({
    branches: sampled.branches,
    terrain: obstacleField,
    players: options.players ?? [],
    shooterId: options.shooterId ?? null,
    bounds,
    hitRadius: options.hitRadius ?? 26,
    collisionStep: options.collisionStep ?? 0.8
  });
  return {
    equation,
    kind: sampled.kind,
    // Both names intentionally point at the obstacle-clipped, ordered paths.
    branches: traced.branches,
    paths: traced.branches,
    sampledBranches: sampled.branches,
    components: sampled.components,
    hitIds: traced.hitIds,
    hits: traced.hitIds,
    hitEvents: traced.hitEvents,
    impacts: traced.impacts,
    firstTerrainImpact: traced.firstTerrainImpact,
    diagnostics: sampled.diagnostics
  };
}

function collectHits(point, players, shooterId, defaultRadius, ids, events, branchIndex, pathIndex) {
  for (const player of players) {
    if (!player || player.alive === false || player.id === shooterId || ids.has(player.id)) continue;
    const center = player.position ?? player;
    const radius = Number(player.hitRadius ?? player.radius ?? defaultRadius);
    if (squaredDistance(point, center) <= radius * radius) {
      ids.add(player.id);
      events.push({ playerId: player.id, point: { ...point }, branchIndex, pathIndex });
    }
  }
}

function isTerrainBlocked(terrain, x, y) {
  if (!terrain) return false;
  if (typeof terrain.isBlocked === "function") return Boolean(terrain.isBlocked(x, y));
  if (typeof terrain.isSolid === "function") return Boolean(terrain.isSolid(x, y));
  return false;
}

/** Refine a free-to-solid segment so curves visibly finish at the obstacle. */
function refineTerrainContact(terrain, freePoint, blockedPoint) {
  let lastFree = { ...freePoint };
  let firstBlocked = { ...blockedPoint };
  // Ten bisections place the endpoint well below a rendered pixel even when
  // collisionStep is at its maximum of four world units.
  for (let iteration = 0; iteration < 10; iteration += 1) {
    const midpoint = lerpPoint(lastFree, firstBlocked, 0.5);
    if (isTerrainBlocked(terrain, midpoint.x, midpoint.y)) {
      firstBlocked = midpoint;
    } else {
      lastFree = midpoint;
    }
  }
  return { lastFree, firstBlocked };
}

/** Apply circular craters after the trace has been animated. */
export function applyTerrainDestruction(terrain, impacts, options = {}) {
  const carve = typeof terrain?.carveCircle === "function"
    ? (x, y, radius) => terrain.carveCircle(x, y, radius)
    : typeof terrain?.destroyCircle === "function"
      ? (x, y, radius) => ({ removed: terrain.destroyCircle(x, y, radius), revision: terrain.revision })
      : null;
  if (!carve) return [];
  const radius = Number(options.radius ?? 15);
  const jitter = Math.max(0, Number(options.radiusJitter ?? 3));
  const random = options.random ?? Math.random;
  const results = [];
  for (const impact of impacts ?? []) {
    if (impact.type !== "terrain") continue;
    const craterRadius = Math.max(1, radius + (random() * 2 - 1) * jitter);
    results.push({
      ...carve(impact.point.x, impact.point.y, craterRadius),
      point: { ...impact.point },
      radius: craterRadius
    });
  }
  return results;
}

/** Compact pixel/tile occupancy grid used by both preview and official traces. */
export class ObstacleGrid {
  constructor(width, height, resolution = 1) {
    if (!(width > 0 && height > 0 && resolution > 0)) {
      throw new TypeError("ObstacleGrid dimensions and resolution must be positive.");
    }
    this.width = Math.ceil(width);
    this.height = Math.ceil(height);
    this.resolution = resolution;
    this.columns = Math.ceil(this.width / resolution);
    this.rows = Math.ceil(this.height / resolution);
    this.data = new Uint8Array(this.columns * this.rows);
    this.revision = 0;
  }

  index(column, row) {
    return row * this.columns + column;
  }

  worldToCell(x, y) {
    return { column: Math.floor(x / this.resolution), row: Math.floor(y / this.resolution) };
  }

  isBlocked(x, y) {
    const { column, row } = this.worldToCell(x, y);
    if (column < 0 || row < 0 || column >= this.columns || row >= this.rows) return false;
    return this.data[this.index(column, row)] !== 0;
  }

  setCell(column, row, blocked = true) {
    if (column < 0 || row < 0 || column >= this.columns || row >= this.rows) return false;
    const index = this.index(column, row);
    const value = blocked ? 1 : 0;
    if (this.data[index] === value) return false;
    this.data[index] = value;
    this.revision += 1;
    return true;
  }

  fillRect(x, y, width, height, blocked = true) {
    const firstColumn = clamp(Math.floor(x / this.resolution), 0, this.columns - 1);
    const lastColumn = clamp(Math.ceil((x + width) / this.resolution) - 1, 0, this.columns - 1);
    const firstRow = clamp(Math.floor(y / this.resolution), 0, this.rows - 1);
    const lastRow = clamp(Math.ceil((y + height) / this.resolution) - 1, 0, this.rows - 1);
    let changed = 0;
    const value = blocked ? 1 : 0;
    for (let row = firstRow; row <= lastRow; row += 1) {
      for (let column = firstColumn; column <= lastColumn; column += 1) {
        const index = this.index(column, row);
        if (this.data[index] !== value) {
          this.data[index] = value;
          changed += 1;
        }
      }
    }
    if (changed) this.revision += 1;
    return changed;
  }

  fillCircle(centerX, centerY, radius, blocked = true) {
    const minColumn = clamp(Math.floor((centerX - radius) / this.resolution), 0, this.columns - 1);
    const maxColumn = clamp(Math.floor((centerX + radius) / this.resolution), 0, this.columns - 1);
    const minRow = clamp(Math.floor((centerY - radius) / this.resolution), 0, this.rows - 1);
    const maxRow = clamp(Math.floor((centerY + radius) / this.resolution), 0, this.rows - 1);
    const radius2 = radius * radius;
    const value = blocked ? 1 : 0;
    let changed = 0;
    for (let row = minRow; row <= maxRow; row += 1) {
      const y = (row + 0.5) * this.resolution;
      for (let column = minColumn; column <= maxColumn; column += 1) {
        const x = (column + 0.5) * this.resolution;
        if ((x - centerX) ** 2 + (y - centerY) ** 2 > radius2) continue;
        const index = this.index(column, row);
        if (this.data[index] !== value) {
          this.data[index] = value;
          changed += 1;
        }
      }
    }
    if (changed) this.revision += 1;
    return changed;
  }

  carveCircle(centerX, centerY, radius) {
    const removed = this.fillCircle(centerX, centerY, radius, false);
    return {
      removed,
      revision: this.revision,
      bounds: {
        x: Math.max(0, centerX - radius),
        y: Math.max(0, centerY - radius),
        width: Math.min(this.width, centerX + radius) - Math.max(0, centerX - radius),
        height: Math.min(this.height, centerY + radius) - Math.max(0, centerY - radius)
      }
    };
  }

  clear() {
    if (this.data.some(Boolean)) {
      this.data.fill(0);
      this.revision += 1;
    }
  }

  clone() {
    const copy = new ObstacleGrid(this.width, this.height, this.resolution);
    copy.data.set(this.data);
    copy.revision = this.revision;
    return copy;
  }

  /** Iterate horizontal occupied runs, useful for fast Canvas rendering. */
  *occupiedRuns() {
    for (let row = 0; row < this.rows; row += 1) {
      let start = -1;
      for (let column = 0; column <= this.columns; column += 1) {
        const occupied = column < this.columns && this.data[this.index(column, row)] !== 0;
        if (occupied && start < 0) start = column;
        if (!occupied && start >= 0) {
          yield {
            x: start * this.resolution,
            y: row * this.resolution,
            width: (column - start) * this.resolution,
            height: this.resolution
          };
          start = -1;
        }
      }
    }
  }
}

/**
 * Build a mathematically exact bot shot, then perturb its parameters according
 * to difficulty. The perfect and fired equations are both returned so the UI
 * can reveal only `equation` while tests/AI can inspect `perfectEquation`.
 */
export function generateBotEquation({
  origin,
  target,
  difficulty = 100,
  random = Math.random,
  style = "mixed",
  maxOffset = 150,
  shapeParameter = null,
  unitPixels = LOCAL_UNIT_PIXELS
}) {
  if (!origin || !target) throw new TypeError("origin and target are required");
  // Callers describe the arena in pixels because that is what terrain, craters
  // and hitboxes are measured in. Everything below fits a curve through the
  // local target, so it all converts to local units first and the emitted
  // coefficients come out in the same units a player would type.
  const unit = resolveUnitPixels(unitPixels);
  const localTarget = worldToLocal(target, origin, unit);
  const maxOffsetUnits = Number(maxOffset) / unit;
  const shapeInUnits = shapeParameter && typeof shapeParameter === "object"
    // arch and wave are y-amounts.
    ? { arch: Number(shapeParameter.arch) / unit, wave: Number(shapeParameter.wave) / unit }
    // A parabola's leading coefficient has units of one over length.
    : (Number.isFinite(shapeParameter) ? Number(shapeParameter) * unit : shapeParameter);
  const distance = Math.max(1 / unit, Math.hypot(localTarget.x, localTarget.y));
  // Select the mathematical family exclusively from the true target. Accuracy
  // is deliberately not consulted until the perfect curve is fully chosen.
  let selectedStyle = style;
  if (selectedStyle === "mixed") {
    const roll = random();
    selectedStyle = roll < 0.4 ? "line" : roll < 0.76 ? "parabola" : "cubic";
  }
  // Keep compatibility with callers that used the former style names without
  // ever generating their now-forbidden implicit equations.
  if (selectedStyle === "implicit-line") selectedStyle = "line";
  if (selectedStyle === "circle") selectedStyle = "cubic";
  if (!new Set(["line", "parabola", "cubic"]).has(selectedStyle)) selectedStyle = "line";

  // Perfect-shape parameters are fixed before difficulty perturbs a copy.
  const baseCurvature = selectedStyle === "parabola"
    ? (Number.isFinite(shapeInUnits)
      ? Number(shapeInUnits)
      : (random() < 0.5 ? -1 : 1) * (0.0007 + random() * 0.0022) * unit)
    : null;
  const baseCubicShape = selectedStyle === "cubic"
    ? normalizeCubicShape(shapeInUnits, distance, random, unit)
    : null;

  const accuracy = clamp(Number(difficulty) / 100, 0, 1);
  const severity = 1 - accuracy;
  // Consume a fixed random pair even at 100%. This keeps the selected perfect
  // family/parameters independent from difficulty across bounded retries.
  const offsetSignRoll = random();
  const offsetMagnitudeRoll = random();
  const signedOffset = severity === 0
    ? 0
    : (offsetSignRoll < 0.5 ? -1 : 1) * maxOffsetUnits * severity * (0.78 + offsetMagnitudeRoll * 0.22);
  const perpendicular = { x: -localTarget.y / distance, y: localTarget.x / distance };
  const aimedTarget = {
    x: localTarget.x + perpendicular.x * signedOffset,
    y: localTarget.y + perpendicular.y * signedOffset
  };

  let perfectEquation;
  let equation;
  let parameters;
  // A graph cannot pass through two different points at x=0. With the game's
  // generous hitboxes, shifting a near-vertical mathematical target by twelve
  // pixels remains a perfect hit while keeping every coefficient finite.
  const fallbackSign = localTarget.x || -localTarget.y || 1;
  const perfectTargetX = functionSafeTargetX(localTarget.x, fallbackSign, unit);
  const firedTargetX = functionSafeTargetX(aimedTarget.x, fallbackSign, unit);
  if (selectedStyle === "line") {
    const perfectSlope = localTarget.y / perfectTargetX;
    const firedSlope = aimedTarget.y / firedTargetX;
    perfectEquation = `f(x) = ${formatNumber(perfectSlope)} * x`;
    equation = `f(x) = ${formatNumber(firedSlope)} * x`;
    parameters = { perfectSlope, firedSlope, perfectTargetX, firedTargetX };
  } else if (selectedStyle === "parabola") {
    const firedCurvature = baseCurvature * (1 + severity * (random() * 0.5 - 0.25));
    const perfectLinear = (localTarget.y - baseCurvature * perfectTargetX ** 2) / perfectTargetX;
    const firedLinear = (aimedTarget.y - firedCurvature * firedTargetX ** 2) / firedTargetX;
    perfectEquation = `f(x) = ${formatNumber(baseCurvature)} * x^2 + ${formatNumber(perfectLinear)} * x`;
    equation = `f(x) = ${formatNumber(firedCurvature)} * x^2 + ${formatNumber(firedLinear)} * x`;
    parameters = {
      baseCurvature,
      perfectLinear,
      firedCurvature,
      firedLinear,
      perfectTargetX,
      firedTargetX
    };
  } else {
    const firedShape = {
      arch: baseCubicShape.arch * (1 + severity * (random() * 0.5 - 0.25)),
      wave: baseCubicShape.wave * (1 + severity * (random() * 0.5 - 0.25))
    };
    perfectEquation = cubicFunctionEquation(perfectTargetX, localTarget.y, baseCubicShape);
    equation = cubicFunctionEquation(firedTargetX, aimedTarget.y, firedShape);
    parameters = {
      perfectShape: baseCubicShape,
      firedShape,
      perfectTargetX,
      firedTargetX
    };
  }

  return {
    style: selectedStyle,
    equation,
    perfectEquation,
    accuracy,
    offset: signedOffset * unit,
    localTarget,
    aimedTarget,
    aimedWorldTarget: localToWorld(aimedTarget, origin, unit),
    unitPixels: unit,
    parameters
  };
}

/**
 * Game-friendly bot facade. `shooter` and `target` may be point objects or
 * player objects with a `.position`. `mapOrField` can be an ObstacleGrid or an
 * object containing `{ bounds, terrain }`.
 */
export function chooseBotShot(shooter, target, difficulty = 100, mapOrField = null, options = {}) {
  const origin = shooter?.position ?? shooter;
  const targetPoint = target?.position ?? target;
  const generated = generateBotEquation({
    origin,
    target: targetPoint,
    difficulty,
    random: options.random ?? Math.random,
    style: options.style ?? "mixed",
    maxOffset: options.maxOffset ?? 150,
    shapeParameter: options.shapeParameter ?? null
  });
  const directTerrain = typeof mapOrField?.isBlocked === "function" || typeof mapOrField?.isSolid === "function"
    ? mapOrField
    : null;
  const terrain = mapOrField?.terrain ?? mapOrField?.obstacleField
    ?? directTerrain
    ?? (mapOrField instanceof ObstacleGrid ? mapOrField : null);
  const bounds = options.bounds ?? mapOrField?.bounds ?? (
    terrain ? makeBounds(terrain.width, terrain.height) : null
  );
  const mathLib = options.math ?? globalThis.math;
  const parsed = mathLib ? parseEquation(generated.equation, mathLib) : null;
  const plan = parsed && bounds
    ? buildCurvePlan(parsed, origin, bounds, terrain, {
      ...options,
      players: options.players ?? (target?.id == null ? [] : [target]),
      shooterId: options.shooterId ?? shooter?.id ?? null
    })
    : null;
  return { ...generated, parsed, plan, target: targetPoint };
}

/** Select a neutral map point for peaceful bots, kept away from live players. */
export function chooseNeutralTarget({ bounds, players = [], margin = 55, random = Math.random, attempts = 80 }) {
  const area = normalizedBounds(bounds);
  let best = null;
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    const point = {
      x: area.x + margin + random() * Math.max(1, area.width - margin * 2),
      y: area.y + margin + random() * Math.max(1, area.height - margin * 2)
    };
    const nearest2 = players.reduce((minimum, player) => {
      const center = player?.position ?? player;
      return center ? Math.min(minimum, squaredDistance(point, center)) : minimum;
    }, Infinity);
    if (!best || nearest2 > best.nearest2) best = { point, nearest2 };
    if (nearest2 >= (margin * 1.8) ** 2) return point;
  }
  return best?.point ?? { x: area.x + area.width / 2, y: area.y + area.height / 2 };
}

function functionSafeTargetX(value, fallbackSign = 1, unitPixels = LOCAL_UNIT_PIXELS) {
  // Twelve pixels, expressed in local units.
  const minimum = 12 / resolveUnitPixels(unitPixels);
  if (Math.abs(value) >= minimum) return value;
  const signSource = value || fallbackSign;
  return signSource < 0 ? -minimum : minimum;
}

function normalizeCubicShape(shapeParameter, distance, random, unitPixels = LOCAL_UNIT_PIXELS) {
  const objectShape = shapeParameter && typeof shapeParameter === "object" ? shapeParameter : null;
  const numericShape = Number.isFinite(shapeParameter) ? Number(shapeParameter) : null;
  // Twenty-four pixels, expressed in local units.
  const scale = Math.max(24 / resolveUnitPixels(unitPixels), distance * 0.36);
  const arch = Number.isFinite(objectShape?.arch)
    ? Number(objectShape.arch)
    : numericShape ?? (random() < 0.5 ? -1 : 1) * scale * (0.45 + random() * 0.55);
  const wave = Number.isFinite(objectShape?.wave)
    ? Number(objectShape.wave)
    : (random() < 0.5 ? -1 : 1) * scale * (0.3 + random() * 0.45);
  return { arch, wave };
}

/**
 * Build a cubic-family graph through local (0, 0) and (targetX, targetY).
 * The normalized arch/wave terms are zero at both endpoints, so changing the
 * shape navigates terrain without sacrificing the mathematically exact aim.
 */
function cubicFunctionEquation(targetX, targetY, shape) {
  const denominator = `(${formatNumber(targetX)})`;
  const normalizedX = `(x / ${denominator})`;
  return `f(x) = ${formatNumber(targetY / targetX)} * x`
    + ` + ${formatNumber(shape.arch)} * ${normalizedX} * (1 - ${normalizedX})`
    + ` + ${formatNumber(shape.wave)} * ${normalizedX} * (1 - ${normalizedX}) * (2 * ${normalizedX} - 1)`;
}

function formatNumber(value) {
  if (Math.abs(value) < 1e-10) return "0";
  return Number(value.toPrecision(10)).toString();
}

function pointInBounds(point, bounds, inset = 0) {
  return point.x >= bounds.x + inset && point.x <= bounds.right - inset
    && point.y >= bounds.y + inset && point.y <= bounds.bottom - inset;
}

function segmentBoundaryIntersection(inside, outside, bounds) {
  const dx = outside.x - inside.x;
  const dy = outside.y - inside.y;
  const candidates = [];
  if (Math.abs(dx) > EPSILON) {
    candidates.push((bounds.x - inside.x) / dx, (bounds.right - inside.x) / dx);
  }
  if (Math.abs(dy) > EPSILON) {
    candidates.push((bounds.y - inside.y) / dy, (bounds.bottom - inside.y) / dy);
  }
  const amount = candidates
    .filter((candidate) => candidate >= 0 && candidate <= 1)
    .sort((a, b) => a - b)
    .find((candidate) => pointInBounds(lerpPoint(inside, outside, candidate), bounds, -EPSILON));
  return amount === undefined ? null : lerpPoint(inside, outside, amount);
}

function projectPointToSegment(point, start, end) {
  const dx = end.x - start.x;
  const dy = end.y - start.y;
  const length2 = dx * dx + dy * dy;
  const amount = length2 <= EPSILON
    ? 0
    : clamp(((point.x - start.x) * dx + (point.y - start.y) * dy) / length2, 0, 1);
  const projected = { x: start.x + dx * amount, y: start.y + dy * amount };
  return { point: projected, amount, distance2: squaredDistance(point, projected) };
}

function polylineDistanceSquared(points, point) {
  if (!points.length) return Infinity;
  if (points.length === 1) return squaredDistance(points[0], point);
  let minimum = Infinity;
  for (let index = 0; index < points.length - 1; index += 1) {
    minimum = Math.min(minimum, projectPointToSegment(point, points[index], points[index + 1]).distance2);
  }
  return minimum;
}

function deduplicateAdjacent(points) {
  const result = [];
  for (const point of points) {
    if (!result.length || squaredDistance(result[result.length - 1], point) > 1e-8) result.push(point);
  }
  return result;
}

function squaredDistance(a, b) {
  return (a.x - b.x) ** 2 + (a.y - b.y) ** 2;
}

function lerpPoint(a, b, amount) {
  return { x: a.x + (b.x - a.x) * amount, y: a.y + (b.y - a.y) * amount };
}

function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}
