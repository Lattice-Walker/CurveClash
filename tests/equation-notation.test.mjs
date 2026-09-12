import test from 'node:test';
import assert from 'node:assert/strict';
import * as math from 'mathjs';

import { cleanMathInput, parseEquation } from '../src/equation-engine.js';

/** Evaluate an equation at a local-unit abscissa, in local units. */
function valueAt(source, x) {
  const equation = parseEquation(source, math);
  return equation.evaluateLocal(x * equation.unitPixels) / equation.unitPixels;
}

test('a Desmos paste keeps its meaning through the normalizer', () => {
  const desmos = String.raw`\sin\left(x\right)+\cos\left(x\right)\sin\left(x\right)+\sqrt{\left(x-10\right)^{2}}-10`;
  assert.equal(cleanMathInput(desmos), 'sin(x)+cos(x)sin(x)+sqrt((x-10)^(2))-10');
  for (const x of [-3, -0.5, 0, 1.25, 4, 12]) {
    const expected = Math.sin(x) + Math.cos(x) * Math.sin(x) + Math.sqrt((x - 10) ** 2) - 10;
    assert.ok(Math.abs(valueAt(desmos, x) - expected) < 1e-9, `f(${x})`);
  }
});

test('\\left and \\right disappear around every bracket they size', () => {
  assert.equal(cleanMathInput(String.raw`\left(x+1\right)^{2}`), '(x+1)^(2)');
  assert.equal(cleanMathInput(String.raw`\left[x\right]+1`), '(x)+1');
});

test('\\frac becomes a division, nested and bare-argument forms included', () => {
  assert.equal(valueAt(String.raw`\frac{x}{2}`, 6), 3);
  assert.equal(valueAt(String.raw`\frac12x`, 6), 3);
  assert.ok(Math.abs(valueAt(String.raw`\frac{\frac{x}{2}}{2}`, 8) - 2) < 1e-12);
});

test('roots accept the braced, degree and radical-sign spellings', () => {
  assert.equal(valueAt(String.raw`\sqrt{x}`, 9), 3);
  assert.ok(Math.abs(valueAt(String.raw`\sqrt[3]{x}`, 27) - 3) < 1e-12);
  assert.equal(valueAt('√(x)', 16), 4);
});

test('unicode superscripts are exponents', () => {
  assert.equal(cleanMathInput('x²'), 'x^(2)');
  assert.equal(valueAt('x²', 5), 25);
  assert.equal(valueAt('x³ - 2x', 3), 21);
  assert.equal(valueAt('x⁻¹', 4), 0.25);
});

test('absolute-value bars compile to abs(), bare and \\left|-paired alike', () => {
  assert.equal(valueAt('|x|', -4), 4);
  assert.equal(valueAt(String.raw`\left|x\right|`, -4), 4);
  assert.equal(valueAt(String.raw`\operatorname{abs}\left(x\right)`, -4), 4);
  assert.equal(valueAt('abs(x)', -4), 4);
  // Two independent bars in one expression, and a bar inside a bar.
  assert.equal(valueAt('|x| + |x - 3|', -1), 5);
  assert.equal(valueAt(String.raw`\left|\left|x\right|-3\right|`, -1), 2);
});

test('a bar or bracket standing next to a value is a product, not a call', () => {
  assert.equal(valueAt('2|x|', -3), 6);
  assert.equal(valueAt(String.raw`\left|x\right|\left(x+1\right)`, -3), 3 * -2);
  assert.equal(valueAt(String.raw`x\left(x+1\right)`, 3), 12);
});

test('LaTeX function names lose their backslash and reach their math.js spelling', () => {
  assert.equal(cleanMathInput(String.raw`\arctan\left(x\right)`), 'atan(x)');
  assert.equal(cleanMathInput(String.raw`\ln\left(x\right)+\pi`), 'log(x)+pi');
  assert.equal(cleanMathInput(String.raw`3\cdot x`), '3* x');
});

test('plain keyboard input is still accepted unchanged', () => {
  for (const source of ['x^2 - 1', '2 * sin(x / 1.5)', '0.01 * x^3 - 0.6 * x', 'exp(x / 3) - 1']) {
    assert.equal(cleanMathInput(source), source, source);
  }
});

test('an unknown function is still refused', () => {
  assert.throws(() => parseEquation(String.raw`\operatorname{rand}\left(x\right)`, math), /not available/);
});

test('a pasted y = ... keeps its left-hand side, but y on the right is still refused', () => {
  assert.equal(valueAt(String.raw`y=x^{2}`, 3), 9);
  assert.equal(valueAt('f(x) = x^2', 3), 9);
  assert.throws(() => parseEquation('y = x + y', math), /cannot use y/);
  assert.throws(() => parseEquation('z = x', math), /equals sign/);
});

test('an equation that is not a function of x is refused', () => {
  const refused = [
    'y^2 = x',
    'y²=x',
    String.raw`y^{2}=\sin\left(x\right)`,
    String.raw`\left|y\right| = x`,
    '2y = x',
    'g(y) = x',
    'y(x) = x',
    'f(y) = x',
    'x^2 + y^2 = 1',
    'x = y',
    'sqrt(y) = x'
  ];
  for (const source of refused) {
    assert.throws(() => parseEquation(source, math), /equals sign|cannot use y|Unknown symbol/, source);
  }
});

test('only y and f(x) may stand on the left of the equals sign', () => {
  assert.equal(valueAt('y = x^2', 3), 9);
  assert.equal(valueAt(' y = x^2 ', 3), 9);
  assert.throws(() => parseEquation('Y = x^2', math), /equals sign/);
  assert.equal(valueAt('f ( x ) = x^2', 3), 9);
});

test('inequalities are refused by name rather than as a broken curve', () => {
  for (const source of ['y > x', 'y >= x^2', String.raw`y\ge x^{2}`, String.raw`y\le x`, 'x < 2']) {
    assert.throws(() => parseEquation(source, math), /inequality/, source);
  }
});
