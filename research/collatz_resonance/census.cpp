// Exact path and indegree-peeling enumerators for the split Collatz odd core.
// Build: c++ -O3 -std=c++17 census.cpp -o census
// Usage: census [positive_d_1_mod_4] [path|peel] [max_vertices]
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

struct Row {
  std::uint64_t minimum, odd_steps, halvings, triple_branches, gcd_with_d;
};

class Core {
 public:
  std::uint64_t d;
  std::uint32_t size;
  Core(std::uint64_t parameter, std::uint64_t budget) : d(parameter) {
    if (d == 0 || d % 4 != 1 || d > (std::numeric_limits<std::uint64_t>::max()-3)/4)
      throw std::invalid_argument("d must be positive, 1 mod 4, and fit the affine arithmetic");
    const auto vertices = (d + 1) / 2;
    if (vertices > budget || vertices > std::numeric_limits<std::uint32_t>::max())
      throw std::invalid_argument("odd core exceeds vertex budget or 32-bit index range");
    size = static_cast<std::uint32_t>(vertices);
  }
  std::uint64_t value(std::uint32_t i) const { return 2ULL * i + 1; }
  std::uint64_t image(std::uint32_t i) const {
    const auto n = value(i);
    return ((n % 4 == 1) ? 3 * n : n) + d;
  }
  std::uint32_t next(std::uint32_t i) const {
    const auto y = image(i);
    return static_cast<std::uint32_t>(((y >> __builtin_ctzll(y)) - 1) / 2);
  }
  Row cycle(std::uint32_t start) const {
    Row row{value(start), 0, 0, 0, 0};
    auto i = start;
    do {
      row.minimum = std::min(row.minimum, value(i));
      ++row.odd_steps;
      row.halvings += __builtin_ctzll(image(i));
      row.triple_branches += value(i) % 4 == 1;
      i = next(i);
    } while (i != start);
    row.gcd_with_d = std::gcd(row.minimum, d);
    return row;
  }
};

std::vector<Row> trace_paths(const Core& graph) {
  std::vector<std::uint8_t> state(graph.size, 0);
  std::vector<Row> result;
  for (std::uint32_t start = 0; start < graph.size; ++start) {
    if (state[start]) continue;
    auto i = start;
    while (state[i] == 0) { state[i] = 1; i = graph.next(i); }
    if (state[i] == 1) result.push_back(graph.cycle(i));
    i = start;
    while (state[i] == 1) { state[i] = 2; i = graph.next(i); }
  }
  return result;
}

std::vector<Row> peel_indegrees(const Core& graph) {
  std::vector<std::uint8_t> indegree(graph.size, 0);
  for (std::uint32_t i = 0; i < graph.size; ++i) {
    auto j = graph.next(i);
    if (indegree[j] == 255) throw std::overflow_error("indegree storage exhausted");
    ++indegree[j];
  }
  std::vector<std::uint32_t> queue;
  queue.reserve(graph.size);
  for (std::uint32_t i = 0; i < graph.size; ++i)
    if (indegree[i] == 0) queue.push_back(i);
  for (std::size_t head = 0; head < queue.size(); ++head) {
    const auto j = graph.next(queue[head]);
    if (--indegree[j] == 0) queue.push_back(j);
  }
  // Each survivor belongs to a cycle. Mark one whole cycle per emitted row.
  std::vector<Row> result;
  for (std::uint32_t i = 0; i < graph.size; ++i) {
    if (indegree[i] == 0) continue;
    result.push_back(graph.cycle(i));
    auto j = i;
    do { indegree[j] = 0; j = graph.next(j); } while (j != i);
  }
  return result;
}

std::uint64_t parse_unsigned(const char* value) {
  const std::string text(value);
  if (text.empty() || text.find_first_not_of("0123456789") != std::string::npos)
    throw std::invalid_argument("expected an unsigned decimal integer");
  std::size_t used = 0;
  const auto result = std::stoull(text, &used);
  if (used != text.size()) throw std::invalid_argument("invalid integer");
  return result;
}

int main(int argc, char** argv) {
  try {
    if (argc > 4) throw std::invalid_argument("usage: census [d] [path|peel] [max_vertices]");
    const auto d = argc > 1 ? parse_unsigned(argv[1]) : 160833217ULL;
    const std::string algorithm = argc > 2 ? argv[2] : "path";
    if (algorithm != "path" && algorithm != "peel")
      throw std::invalid_argument("algorithm must be path or peel");
    const auto budget = argc > 3 ? parse_unsigned(argv[3]) : 100000000ULL;
    const Core graph(d, budget);
    auto rows = algorithm == "path" ? trace_paths(graph) : peel_indegrees(graph);
    std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) { return a.minimum < b.minimum; });
    std::cout << "cycle_minimum,odd_steps,halvings,triple_branches,gcd_with_d\n";
    for (const auto& row : rows)
      std::cout << row.minimum << ',' << row.odd_steps << ',' << row.halvings << ','
                << row.triple_branches << ',' << row.gcd_with_d << '\n';
  } catch (const std::exception& error) {
    std::cerr << "census: " << error.what() << '\n';
    return 2;
  }
}
