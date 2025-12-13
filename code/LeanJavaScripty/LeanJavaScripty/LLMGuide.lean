import Lean.Data.Json

open Lean

-- 1. OLLAMA REQUEST/RESPONSE TYPES
-- We define the JSON structure that Ollama expects/returns

structure OllamaRequest where
  model : String
  prompt : String
  stream : Bool := false -- Turn off streaming to get one JSON blob
deriving ToJson, FromJson

structure OllamaResponse where
  response : String
  done : Bool
deriving ToJson, FromJson

-- 2. THE HELPER: CALLING CURL
-- This function executes a shell command to POST data to your local API.

def callOllama (prompt : String) : IO String := do
  let reqBody := { model := "llama3", prompt := prompt, stream := false : OllamaRequest }
  let jsonStr := toJson reqBody |>.compress

  -- Shell out to cURL
  let out <- IO.Process.run {
    cmd := "curl",
    args := #["-X", "POST", "http://localhost:11434/api/generate", "-d", jsonStr]
  }

  -- Parse the JSON response
  match Json.parse out with
  | Except.error e => throw (IO.userError s!"JSON Parse Error: {e}")
  | Except.ok json =>
      match fromJson? (α := OllamaResponse) json with
      | Except.error e => throw (IO.userError s!"Structure Error: {e}")
      | Except.ok resp => return resp.response
