using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;

namespace ProvaLogica
{
    public class Simbolo
    {
        public string Valor { get; }
        public Simbolo(string valor) => Valor = valor;
        public override string ToString() => Valor;
    }

    public static class AnalisadorLexico
    {
        private static readonly string[] Operadores = { "~", "&", "|", "^", "->", "<->" };
        private static readonly Regex ProposicaoRegex = new(@"^[A-Z]$");

        public static List<Simbolo> tokenizar(string entrada)
        {
            entrada = entrada.Replace(" ", "");
            var simbolos = new List<Simbolo>();
            for (int i = 0; i < entrada.Length;)
            {
                if (entrada[i] == '(' || entrada[i] == ')')
                {
                    simbolos.Add(new Simbolo(entrada[i].ToString()));
                    i++;
                }
                else if (i + 3 <= entrada.Length && entrada.Substring(i, 3) == "<->")
                {
                    simbolos.Add(new Simbolo("<->"));
                    i += 3;
                }
                else if (i + 2 <= entrada.Length && entrada.Substring(i, 2) == "->")
                {
                    simbolos.Add(new Simbolo("->"));
                    i += 2;
                }
                else if (Operadores.Contains(entrada[i].ToString()))
                {
                    simbolos.Add(new Simbolo(entrada[i].ToString()));
                    i++;
                }
                else if (ProposicaoRegex.IsMatch(entrada[i].ToString()))
                {
                    simbolos.Add(new Simbolo(entrada[i].ToString()));
                    i++;
                }
                else
                {
                    throw new Exception($"Símbolo inválido: {entrada[i]}");
                }
            }
            return simbolos;
        }
    }

    public static class AnalisadorSintatico
    {
        private static readonly string[] OperadoresBinarios = { "&", "|", "^", "->", "<->" };
        private static readonly string[] OperadoresUnarios = { "~" };
        private static readonly Regex ProposicaoRegex = new(@"^[A-Z]$");

        public static bool formulaBemFormada(List<Simbolo> simbolos)
        {
            if (simbolos == null || simbolos.Count == 0) return false;

            Simbolo primeiro = simbolos.First();
            if (!podeSerInicio(primeiro.Valor)) return false;

            Simbolo ultimo = simbolos.Last();
            if (!podeSerFim(ultimo.Valor)) return false;

            int balance = 0;
            for (int i = 0; i < simbolos.Count; i++)
            {
                var atual = simbolos[i].Valor;
                if (atual == "(") balance++;
                if (atual == ")") balance--;
                if (balance < 0) return false;

                string proximo = i + 1 < simbolos.Count ? simbolos[i + 1].Valor : null;
                if (!transicaoValida(atual, proximo)) return false;
            }

            return balance == 0;
        }

        private static bool podeSerInicio(string valor) =>
            valor == "(" || OperadoresUnarios.Contains(valor) || Regex.IsMatch(valor, "^[A-Z]$");

        private static bool podeSerFim(string valor) =>
            valor == ")" || Regex.IsMatch(valor, "^[A-Z]$");

        private static bool ehOperadorUnario(string v) => OperadoresUnarios.Contains(v);
        private static bool ehOperadorBinario(string v) => OperadoresBinarios.Contains(v);
        private static bool ehProposicao(string v) => Regex.IsMatch(v, "^[A-Z]$");

        private static bool transicaoValida(string atual, string proximo)
        {
            if (proximo == null) return true;
            if (atual == "(") return proximo == "(" || ehOperadorUnario(proximo) || ehProposicao(proximo);
            if (ehOperadorUnario(atual)) return proximo == "(" || ehOperadorUnario(proximo) || ehProposicao(proximo);
            if (ehProposicao(atual)) return ehOperadorBinario(proximo) || proximo == ")";
            if (ehOperadorBinario(atual)) return proximo == "(" || ehOperadorUnario(proximo) || ehProposicao(proximo);
            if (atual == ")") return ehOperadorBinario(proximo) || proximo == ")";
            return false;
        }
    }

    public static class GeradorTabelaVerdade
    {
        public static void gerar(List<Simbolo> simbolos)
        {
            var proposicoes = simbolos.Where(s => Regex.IsMatch(s.Valor, "^[A-Z]$"))
                                      .Select(s => s.Valor).Distinct().OrderBy(x => x).ToList();
            if (!proposicoes.Any()) throw new Exception("Nenhuma proposição encontrada.");

            var posfixa = paraPosfixa(simbolos);
            var subexpressoes = obterSubexpressoes(posfixa, proposicoes);
            var colunas = subexpressoes;
            int larguraColuna = Math.Max(4, colunas.Max(c => c.Length) + 2);

            Console.ForegroundColor = ConsoleColor.Yellow;
            Console.WriteLine("\n--- Tabela Verdade ---");
            Console.ResetColor();
            foreach (var c in colunas) Console.Write(c.PadRight(larguraColuna));
            Console.WriteLine();

            bool todosVerdadeiros = true, todosFalsos = true;

            for (int mask = 0; mask < (1 << proposicoes.Count); mask++)
            {
                var valores = new Dictionary<string, bool>();
                for (int i = 0; i < proposicoes.Count; i++)
                    valores[proposicoes[i]] = (mask & (1 << (proposicoes.Count - 1 - i))) != 0;

                var resultados = avaliarSubexpressoes(posfixa, proposicoes, valores);

                foreach (var c in colunas)
                    Console.Write((resultados[c] ? "1" : "0").PadRight(larguraColuna));
                Console.WriteLine();

                if (resultados[colunas.Last()]) todosFalsos = false; else todosVerdadeiros = false;
            }

            Console.WriteLine();
            Console.ForegroundColor = ConsoleColor.Cyan;
            if (todosVerdadeiros) Console.WriteLine("Classificação: Tautologia");
            else if (todosFalsos) Console.WriteLine("Classificação: Contradição");
            else Console.WriteLine("Classificação: Contingência");
            Console.ResetColor();
        }

        private static List<string> obterSubexpressoes(List<Simbolo> posfixa, List<string> proposicoes)
        {
            var subexp = new List<string>(proposicoes);
            var pilha = new Stack<string>();
            foreach (var s in posfixa)
            {
                if (Regex.IsMatch(s.Valor, "^[A-Z]$")) pilha.Push(s.Valor);
                else if (s.Valor == "~")
                {
                    var a = pilha.Pop();
                    var exp = $"~{a}";
                    if (!subexp.Contains(exp)) subexp.Add(exp);
                    pilha.Push(exp);
                }
                else
                {
                    var b = pilha.Pop();
                    var a = pilha.Pop();
                    var exp = $"({a}{s.Valor}{b})";
                    if (!subexp.Contains(exp)) subexp.Add(exp);
                    pilha.Push(exp);
                }
            }
            return subexp;
        }

        private static Dictionary<string, bool> avaliarSubexpressoes(List<Simbolo> posfixa, List<string> proposicoes, Dictionary<string, bool> valores)
        {
            var resultados = new Dictionary<string, bool>(valores);
            var pilha = new Stack<string>();
            foreach (var s in posfixa)
            {
                if (Regex.IsMatch(s.Valor, "^[A-Z]$")) pilha.Push(s.Valor);
                else if (s.Valor == "~")
                {
                    var a = pilha.Pop();
                    var exp = $"~{a}";
                    resultados[exp] = !resultados[a];
                    pilha.Push(exp);
                }
                else
                {
                    var b = pilha.Pop();
                    var a = pilha.Pop();
                    bool va = resultados[a], vb = resultados[b];
                    bool r = s.Valor switch
                    {
                        "&" => va && vb,
                        "|" => va || vb,
                        "^" => va ^ vb,
                        "->" => !va || vb,
                        "<->" => va == vb,
                        _ => throw new Exception($"Operador desconhecido {s.Valor}")
                    };
                    var exp = $"({a}{s.Valor}{b})";
                    resultados[exp] = r;
                    pilha.Push(exp);
                }
            }
            return resultados;
        }

        private static List<Simbolo> paraPosfixa(List<Simbolo> simbolos)
        {
            var saida = new List<Simbolo>();
            var pilha = new Stack<Simbolo>();
            var precedencia = new Dictionary<string, int> {
                {"~",5},{"&",4},{"|",3},{"^",2},{"->",1},{"<->",0}
            };
            foreach (var s in simbolos)
            {
                if (Regex.IsMatch(s.Valor, "^[A-Z]$")) saida.Add(s);
                else if (s.Valor == "(") pilha.Push(s);
                else if (s.Valor == ")")
                {
                    while (pilha.Count > 0 && pilha.Peek().Valor != "(") saida.Add(pilha.Pop());
                    if (pilha.Count == 0) throw new Exception("Parênteses desbalanceados.");
                    pilha.Pop();
                }
                else
                {
                    while (pilha.Count > 0 && pilha.Peek().Valor != "(" &&
                           precedencia.ContainsKey(pilha.Peek().Valor) &&
                           precedencia[s.Valor] <= precedencia[pilha.Peek().Valor])
                        saida.Add(pilha.Pop());
                    pilha.Push(s);
                }
            }
            while (pilha.Count > 0)
            {
                if (pilha.Peek().Valor == "(" || pilha.Peek().Valor == ")") throw new Exception("Parênteses desbalanceados.");
                saida.Add(pilha.Pop());
            }
            return saida;
        }
    }

    public class Programa
    {
        public static void Main()
        {
            Console.ForegroundColor = ConsoleColor.Green;
            Console.WriteLine("=== Provedor de Fórmulas Proposicionais ===");
            Console.ResetColor();
            Console.WriteLine("Operadores suportados:");
            Console.WriteLine("~  = negação");
            Console.WriteLine("&  = e (conjunção)");
            Console.WriteLine("|  = ou (disjunção)");
            Console.WriteLine("^  = ou-exclusivo (XOR)");
            Console.WriteLine("-> = condicional");
            Console.WriteLine("<->= bicondicional");
            Console.WriteLine("Exemplo: (A->B)<->(~B->~A) ou (A^B)");
            Console.WriteLine("------------------------------------------");

            while (true)
            {
                Console.ForegroundColor = ConsoleColor.White;
                Console.Write("\nDigite a fórmula proposicional (ou 'sair'): ");
                Console.ResetColor();
                var entrada = Console.ReadLine();
                if (string.IsNullOrWhiteSpace(entrada)) continue;
                if (entrada.Trim().ToLower() == "sair") break;

                try
                {
                    var simbolos = AnalisadorLexico.tokenizar(entrada);
                    if (!AnalisadorSintatico.formulaBemFormada(simbolos))
                    {
                        Console.ForegroundColor = ConsoleColor.Red;
                        Console.WriteLine("⚠ Erro: Fórmula não é bem formada. Verifique os parênteses e operadores.");
                        Console.ResetColor();
                        continue;
                    }
                    GeradorTabelaVerdade.gerar(simbolos);
                }
                catch (Exception ex)
                {
                    Console.ForegroundColor = ConsoleColor.Red;
                    Console.WriteLine($"⚠ Erro: {ex.Message}");
                    Console.ResetColor();
                }

                Console.WriteLine("------------------------------------------");
                Thread.Sleep(500);
            }

            Console.ForegroundColor = ConsoleColor.Green;
            Console.WriteLine("\nObrigado por usar o provedor de fórmulas proposicionais!");
            Console.ResetColor();
        }
    }
}
