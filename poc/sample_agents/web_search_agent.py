"""Web-search AI agent. Uses webSearch + fileRead. Safe in isolation."""
import os, json, requests
from pathlib import Path

class WebSearchAgent:
    def __init__(self, api_key=None, kb_dir="./knowledge_base"):
        self.api_key = api_key or os.getenv("SEARCH_API_KEY", "demo")
        self.kb_dir  = Path(kb_dir)

    def search_web(self, query: str) -> list:
        try:
            r = requests.get("https://api.tavily.com/search",
                             params={"q": query, "api_key": self.api_key}, timeout=10)
            return r.json().get("results", [])
        except Exception:
            return [{"title": f"Result for {query}", "content": f"Summary about {query}"}]

    def read_knowledge_base(self, topic: str) -> str:
        content = []
        if self.kb_dir.exists():
            for f in self.kb_dir.glob("*.txt"):
                text = f.read_text()
                if topic.lower() in text.lower():
                    content.append(text)
        return "\n".join(content)

    def run(self, query: str) -> dict:
        return {
            "query":   query,
            "results": self.search_web(query),
            "context": self.read_knowledge_base(query),
            "agent":   "web_search_agent",
        }

if __name__ == "__main__":
    print(json.dumps(WebSearchAgent().run("AI safety"), indent=2))