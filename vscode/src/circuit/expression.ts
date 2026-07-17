import type { ParameterExpression } from "./model";

type Token =
  | { kind: "number"; value: string }
  | { kind: "pi" }
  | { kind: "symbol"; value: string }
  | { kind: "end" };

function tokenize(source: string): Token[] {
  const tokens: Token[] = [];
  let index = 0;
  while (index < source.length) {
    const rest = source.slice(index);
    const whitespace = /^\s+/.exec(rest);
    if (whitespace) {
      index += whitespace[0].length;
      continue;
    }
    const number = /^(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?/.exec(rest);
    if (number) {
      tokens.push({ kind: "number", value: number[0] });
      index += number[0].length;
      continue;
    }
    if (rest.startsWith("pi") && !/[A-Za-z0-9_]/.test(rest[2] ?? "")) {
      tokens.push({ kind: "pi" });
      index += 2;
      continue;
    }
    if (rest.startsWith("π")) {
      tokens.push({ kind: "pi" });
      index += 1;
      continue;
    }
    const symbol = rest[0];
    if (symbol && "+-*/()".includes(symbol)) {
      tokens.push({ kind: "symbol", value: symbol });
      index += 1;
      continue;
    }
    throw new Error(`unsupported parameter token near '${rest.slice(0, 12)}'`);
  }
  tokens.push({ kind: "end" });
  return tokens;
}

class ExpressionParser {
  private index = 0;
  constructor(private readonly tokens: Token[]) {}

  parse(): ParameterExpression {
    const expression = this.parseBinary(0);
    if (this.peek().kind !== "end") throw new Error("unexpected trailing parameter text");
    return expression;
  }

  private peek(): Token {
    return this.tokens[this.index] ?? { kind: "end" };
  }

  private consume(): Token {
    const token = this.peek();
    this.index += 1;
    return token;
  }

  private parseBinary(minimumPrecedence: number): ParameterExpression {
    let left = this.parseUnary();
    while (true) {
      const token = this.peek();
      if (token.kind !== "symbol" || !"+-*/".includes(token.value)) break;
      const precedence = token.value === "+" || token.value === "-" ? 10 : 20;
      if (precedence < minimumPrecedence) break;
      this.consume();
      const right = this.parseBinary(precedence + 1);
      left = {
        kind: "binary",
        operator: token.value as "+" | "-" | "*" | "/",
        left,
        right,
      };
    }
    return left;
  }

  private parseUnary(): ParameterExpression {
    const token = this.peek();
    if (token.kind === "symbol" && (token.value === "+" || token.value === "-")) {
      this.consume();
      return { kind: "unary", operator: token.value, operand: this.parseUnary() };
    }
    if (token.kind === "number") {
      this.consume();
      return { kind: "number", value: token.value };
    }
    if (token.kind === "pi") {
      this.consume();
      return { kind: "pi" };
    }
    if (token.kind === "symbol" && token.value === "(") {
      this.consume();
      const expression = this.parseBinary(0);
      const closing = this.consume();
      if (closing.kind !== "symbol" || closing.value !== ")") {
        throw new Error("parameter expression is missing ')'");
      }
      return expression;
    }
    throw new Error("expected a number, pi, sign, or parenthesized parameter expression");
  }
}

export function parseParameterExpression(source: string): ParameterExpression {
  if (!source.trim()) throw new Error("parameter expression cannot be empty");
  return new ExpressionParser(tokenize(source)).parse();
}

function precedence(expression: ParameterExpression): number {
  if (expression.kind === "binary")
    return expression.operator === "+" || expression.operator === "-" ? 10 : 20;
  if (expression.kind === "unary") return 30;
  return 40;
}

export function serializeParameterExpression(
  expression: ParameterExpression,
  parentPrecedence = 0,
): string {
  if (expression.kind === "number") return expression.value;
  if (expression.kind === "pi") return "pi";
  if (expression.kind === "unary") {
    const value = `${expression.operator}${serializeParameterExpression(expression.operand, 30)}`;
    return 30 < parentPrecedence ? `(${value})` : value;
  }
  const ownPrecedence = precedence(expression);
  const left = serializeParameterExpression(expression.left, ownPrecedence);
  const right = serializeParameterExpression(expression.right, ownPrecedence + 1);
  const value = `${left} ${expression.operator} ${right}`;
  return ownPrecedence < parentPrecedence ? `(${value})` : value;
}
