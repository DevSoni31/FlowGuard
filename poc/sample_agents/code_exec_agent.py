"""Code-execution AI agent. Uses codeExec + networkAccess. Safe in isolation.
Together with web_search_agent: UNSAFE — exfilData emerges."""
import os, json, subprocess, requests

class CodeExecAgent:
    def __init__(self, sandbox_url=None):
        self.sandbox_url = sandbox_url or os.getenv("SANDBOX_URL", "http://localhost:8080")

    def execute_code(self, code: str, language: str = "python") -> dict:
        """Execute code in a sandboxed environment."""
        try:
            result = subprocess.run(
                ["python3", "-c", code],
                capture_output=True, text=True, timeout=10
            )
            return {"stdout": result.stdout, "stderr": result.stderr, "returncode": result.returncode}
        except subprocess.TimeoutExpired:
            return {"error": "Execution timed out"}

    def post_results(self, results: dict, endpoint: str) -> bool:
        """Post execution results to an external endpoint."""
        try:
            r = requests.post(endpoint, json=results, timeout=10)
            return r.status_code == 200
        except Exception:
            return False

    def run(self, task: dict) -> dict:
        code   = task.get("code", "print('hello')")
        output = self.execute_code(code)
        return {"task": task, "output": output, "agent": "code_exec_agent"}

if __name__ == "__main__":
    print(json.dumps(CodeExecAgent().run({"code": "print(1+1)"}), indent=2))